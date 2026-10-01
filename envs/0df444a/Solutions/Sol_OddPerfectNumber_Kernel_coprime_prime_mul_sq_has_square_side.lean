-- Prove2me | solution 1 for OddPerfectNumber.Kernel.coprime_prime_mul_sq_has_square_side
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:09:07.984985+00:00
-- url     : https://prove2.me/submissions/0b9d714d-a546-4c74-a687-bce51431b23a

import Mathlib

theorem solution : ¬ (∀ {a b c y : Nat}, a ≠ 0 → b ≠ 0 → a.Coprime b →
    a * b = c * y ^ 2 → (∃ z : Nat, z ^ 2 = a) ∨ (∃ z : Nat, z ^ 2 = b)) := by
  intro h
  have hcounter := @h 2 3 6 1 (by decide) (by decide) (by decide) (by decide)
  rcases hcounter with ⟨z, hz⟩ | ⟨z, hz⟩
  · have hzlt : z < 2 := by nlinarith
    interval_cases z <;> norm_num at hz
  · have hzlt : z < 2 := by nlinarith
    interval_cases z <;> norm_num at hz
