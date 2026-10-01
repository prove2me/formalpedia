-- Prove2me | solution 2 for burau_cf_std_neg_inv_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:16:35.868299+00:00
-- url     : https://prove2.me/submissions/d7443837-86c1-4811-a174-81d1deee449e

import Definitions.Def_burau_std_cf

set_option autoImplicit false

/-- **Branch `b/a ≥ 2` of the negative-reciprocal rule** (normalisation-free derived form). -/
theorem solution (a b : ℤ) (ha : 0 < a) (h : 2 ≤ b / a) :
    cfStd b (-a) = [-1, a / (b - a) + 1] ++ cfStd (a % (b - a)) (b - a) := by
  have h1 : 1 ≤ b / a := by omega
  have hd := Int.mul_ediv_add_emod b a
  have h0 : 0 ≤ b % a := Int.emod_nonneg b (ne_of_gt ha)
  have hk : a * 2 ≤ a * (b / a) := Int.mul_le_mul_of_nonneg_left h ha.le
  have hb : b ≠ 0 := by omega
  have hba : b - a ≠ 0 := by omega
  have hle : 0 ≤ b - a := by omega
  have hlt : b - a < b := by omega
  have hediv : (-a) / b = -1 := by
    have hlt' : b - a < |b| := by
      rw [abs_of_pos (by omega : (0 : ℤ) < b)]
      exact hlt
    calc (-a) / b = ((b - a) + b * (-1)) / b := by
          congr 1
          ring
      _ = (b - a) / b + (-1) := by rw [Int.add_mul_ediv_left (b - a) (-1) hb]
      _ = 0 + (-1) := by rw [Int.ediv_eq_zero_of_lt_abs hle hlt']
      _ = -1 := by ring
  have hemod : (-a) % b = b - a := by
    calc (-a) % b = ((b - a) + b * (-1)) % b := by
          congr 2
          ring
      _ = (b - a) % b := by rw [Int.add_mul_emod_self_left]
      _ = b - a := Int.emod_eq_of_lt hle hlt
  have hadd : cfStd (b - a) ((b - a) + a)
      = (a / (b - a) + 1) :: cfStd (a % (b - a)) (b - a) := by
    rw [cfStd_cons (b - a) ((b - a) + a) hba]
    have hdiv : ((b - a) + a) / (b - a) = a / (b - a) + 1 := by
      rw [show (b - a) + a = a + (b - a) * 1 by ring, Int.add_mul_ediv_left a 1 hba]
    have hmod : ((b - a) + a) % (b - a) = a % (b - a) := by
      rw [show (b - a) + a = a + (b - a) * 1 by ring, Int.add_mul_emod_self_left]
    rw [hdiv, hmod]
  rw [cfStd_cons b (-a) hb, hediv, hemod]
  rw [show b = (b - a) + a by ring]
  rw [show (b - a) + a - a = b - a by ring]
  rw [hadd]
  rfl
