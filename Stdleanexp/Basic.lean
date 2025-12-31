
example (a b c : Nat) : a*(b+c) + a*b = a*b + a*c + a*b := by
  rw[Nat.left_distrib]

example (a b c d: Nat) : (a + (b + c)) + d = d + (c + a + b) := by
  ac_rfl

example (a b c d: Nat) : (a * (b * c)) * d = d * (c * a * b) := by
  ac_rfl

example ( c : Nat) : c+c = 2*c := by
    calc c + c
      = c*1 + c*1  := by rw[Nat.mul_one]
    _ = c*(1+1)    := by rw[Nat.left_distrib]
    _ = 2*c        := by ac_rfl


example (c: Nat) : c+c = 2*c := by
  let h: c+c = c*1+c*1 := by rw[Nat.mul_one c]
  rw[h]
  rw[<-Nat.left_distrib]
  rw[Nat.mul_comm]
