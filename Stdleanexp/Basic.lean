
def hello := "world"

example (a b c : Nat) : a*(b+c) + a*b = a*b + a*c + a*b := by
  rw[Nat.left_distrib]

example (a b c d: Nat) : (a + (b + c)) + d = d + (c + a + b) := by
  ac_rfl
