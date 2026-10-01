-- Prove2me | solution 2 for burau_cf_std_neg_inv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:09:14.102894+00:00
-- url     : https://prove2.me/submissions/b5bfbb12-372d-4b81-a4d3-f005ce45c4f4

import Definitions.Def_burau_std_cf

set_option autoImplicit false

/-- **Branch `b/a = 1` of the negative-reciprocal rule**: the tail `cfStd (b-a) b` is the tail of
`cfStd (b-a) a` with its head increased by one. -/
theorem solution (a b : ℤ) (ha : 0 < a) (h : b / a = 1) :
    cfStd b (-a) = [-1] ++ (match cfStd (b - a) a with
                            | [] => []
                            | y :: ys => (y + 1) :: ys) := by
  have hd := Int.mul_ediv_add_emod b a
  have h1 : 0 ≤ b % a := Int.emod_nonneg b (ne_of_gt ha)
  have h1le : 1 ≤ b / a := by omega
  have hk : a * 1 ≤ a * (b / a) := Int.mul_le_mul_of_nonneg_left h1le ha.le
  have hb : b ≠ 0 := by omega
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
  rw [cfStd_cons b (-a) hb, hediv, hemod]
  by_cases hba : b - a = 0
  · have hb0 : b = a := by omega
    rw [hb0]
    rw [show a - a = 0 by ring, cfStd_zero]
    rfl
  · have hadd : cfStd (b - a) ((b - a) + a)
        = (a / (b - a) + 1) :: cfStd (a % (b - a)) (b - a) := by
      rw [cfStd_cons (b - a) ((b - a) + a) hba]
      have hdiv : ((b - a) + a) / (b - a) = a / (b - a) + 1 := by
        rw [show (b - a) + a = a + (b - a) * 1 by ring, Int.add_mul_ediv_left a 1 hba]
      have hmod : ((b - a) + a) % (b - a) = a % (b - a) := by
        rw [show (b - a) + a = a + (b - a) * 1 by ring, Int.add_mul_emod_self_left]
      rw [hdiv, hmod]
    rw [show b = (b - a) + a by ring]
    rw [show (b - a) + a - a = b - a by ring]
    rw [hadd, cfStd_cons (b - a) a hba]
    rfl
