-- Prove2me | solution 1 for OddPerfectNumber.Kernel.second_block_gcd_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T02:31:11.822147+00:00
-- url     : https://prove2.me/submissions/6f8da4e1-0f53-4f9b-9a1b-070ad5c26639

import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_second_block_gcd_dvd_three

namespace OddPerfectNumber.Kernel
namespace GcdCases

/-- The gcd of `(p + 1) / 2` and `p ^ 2 - p + 1` is `1` or `3` when
`p % 4 = 1`.  This is the case split that the accepted divisibility child
`second_block_gcd_dvd_three` leaves open: it gives only `Nat.gcd A B | 3`,
and since `3` is prime the gcd is `1` or `3`.

The `1` branch is the coprime case in which `coprime_sq_factor_right` forces
`p ^ 2 - p + 1` to be a square; the `3` branch is the branch in which
`p ^ 2 - p + 1` is three times a square. -/
theorem solution_aux (p : Nat) (hp4 : p % 4 = 1) :
    Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 1 ∨
      Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 3 := by
  have hdvd3 : Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) ∣ 3 :=
    OddPerfectNumber.Kernel.second_block_gcd_dvd_three p hp4
  -- `Nat.dvd_prime` is applied to the modulus that actually occurs, namely
  -- `3`, and not to the primality hypothesis on `p`.
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
  · exact Or.inl h
  · exact Or.inr h

end GcdCases
end OddPerfectNumber.Kernel

theorem solution (p : Nat) (hp4 : p % 4 = 1) :
    Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 1 ∨
      Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 3 :=
  OddPerfectNumber.Kernel.GcdCases.solution_aux p hp4
