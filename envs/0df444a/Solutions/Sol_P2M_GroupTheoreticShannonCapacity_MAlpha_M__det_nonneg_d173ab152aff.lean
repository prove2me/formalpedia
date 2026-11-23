-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:33.359201+00:00
-- url     : https://prove2.me/submissions/76f43184-9c58-432c-8623-4843b5a2c49d

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    (Mα n α).det ≥ 0 := by
  cases n with
  | zero =>
    -- 0×0 matrix has det = 1
    rw [Matrix.det_fin_zero]
    linarith
  | succ m =>
    have hn : 1 ≤ m + 1 := by omega
    have hα_ne : α ≠ -1 := by linarith
    rw [Mα_det (m + 1) hn α hα_ne]
    -- det = ((-1)^n * α + α^n) / ((-1)^n * α + (-1)^n)
    -- For α ∈ [0,1], both numerator and denominator have the same sign
    have hdenom_ne : (-1 : ℝ)^(m + 1) * α + (-1)^(m + 1) ≠ 0 := by
      have hfactor : (-1 : ℝ)^(m + 1) * α + (-1)^(m + 1) = (-1)^(m + 1) * (α + 1) := by ring
      rw [hfactor]
      intro h
      have hpow_ne : (-1 : ℝ)^(m + 1) ≠ 0 := by
        rcases neg_one_pow_eq_or ℝ (m + 1) with hp | hp <;> simp [hp]
      have : α + 1 = 0 := (mul_eq_zero.mp h).resolve_left hpow_ne
      linarith
    rw [ge_iff_le, ← sub_nonneg, sub_zero, div_nonneg_iff]
    rcases neg_one_pow_eq_or ℝ (m + 1) with heven | hodd
    · -- Case (-1)^n = 1 (n even)
      left
      constructor
      · -- Numerator: α + α^n ≥ 0
        simp only [heven, one_mul]
        have : α^(m + 1) ≥ 0 := pow_nonneg hα _
        linarith
      · -- Denominator: α + 1 > 0
        simp only [heven, one_mul]
        linarith
    · -- Case (-1)^n = -1 (n odd)
      right
      constructor
      · -- Numerator: -α + α^n ≤ 0
        simp only [hodd, neg_one_mul, neg_add_le_iff_le_add, add_zero]
        -- Need α^n ≤ α, i.e., α^{n-1} ≤ 1 when α ≤ 1
        calc α^(m + 1) = α * α^m := by ring
          _ ≤ α * 1 := by {
            apply mul_le_mul_of_nonneg_left _ hα
            exact pow_le_one₀ hα hα'
          }
          _ = α := by ring
      · -- Denominator: -(α + 1) < 0
        simp only [hodd, neg_one_mul]
        linarith
end GroupTheoreticShannonCapacity.MAlpha
