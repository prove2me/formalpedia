-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_odd_p_source_is_middle_or_square_part
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:32:32.948007+00:00
-- url     : https://prove2.me/submissions/c85cf118-4874-4ec6-a001-00706f992a70

import Mathlib

/-! Disproof of 7d5867b0 `OddPerfectNumber.Kernel.five_odd_p_source_is_middle_or_square_part`.

`q` and `r` are arbitrary naturals, and `t != q` does not prevent `t ∣ q`.
Witness: `m = 30`, `u = a = b = d1 = 1`, `q = 10`, `r = 1`, `t = 5`. -/

set_option autoImplicit false

theorem solution : ¬ (∀ (m u a b d1 q r t : Nat)
    (hshape : m = 3 * u * a * b * d1 * q * r)
    (ht : t.Prime)
    (htd : Dvd.dvd t m)
    (ht3 : t != 3) (htq : t != q) (htr : t != r),
    t = q ∨ Dvd.dvd t (u * a * b * d1) ∨ t = r) := by
  intro h
  have h5 := h 30 1 1 1 1 10 1 5 (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  omega
