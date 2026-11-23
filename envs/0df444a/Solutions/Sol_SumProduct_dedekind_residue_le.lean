-- Prove2me | solution 1 for SumProduct.dedekind_residue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:22:59.679402+00:00
-- url     : https://prove2.me/submissions/e591b27d-3e34-46a1-bf10-de9fe5c56698

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
import Theorems.Thm_SumProduct_dedekindZeta_completed_residue_le
import Theorems.Thm_SumProduct_dedekindZeta_two_re_le


set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (_hd : 2 ≤ Module.finrank ℚ K) :
    NumberField.dedekindZeta_residue K
      ≤ 2 * (2 / Real.pi) ^ Module.finrank ℚ K * Real.sqrt |(NumberField.discr K : ℝ)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `ζ_K(2) ≤ 2^d = (2/(2-1))^d`, the proved Euler-product bound.
  have hζ : (NumberField.dedekindZeta K (2 : ℂ)).re ≤ (2 / (2 - 1)) ^ Module.finrank ℚ K :=
    dedekindZeta_two_re_le.trans_eq (by rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num])
  refine ((dedekindZeta_completed_residue_le K 2 one_lt_two).trans
    (mul_le_mul_of_nonneg_left hζ ?_)).trans_eq ?_
  · -- the prefactor `2(2-1)|Δ|^{1/2}π^{-d}Γ(1)^d` is nonnegative
    have hb : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| ^ (((2 : ℝ) - 1) / 2) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hc : (0 : ℝ) ≤ Real.pi ^ (-(Module.finrank ℚ K : ℝ) * 2 / 2) :=
      (Real.rpow_pos_of_pos hpi _).le
    have hg : (0 : ℝ) ≤ Real.Gamma ((2 : ℝ) / 2) ^ Module.finrank ℚ K :=
      pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) hb) hc) hg
  set d := Module.finrank ℚ K with hddef
  have e1 : ((2 : ℝ) - 1) = 1 := by norm_num
  have eΓ : Real.Gamma ((2 : ℝ) / 2) = 1 := by
    rw [show (2 : ℝ) / 2 = 1 by norm_num]; exact Real.Gamma_one
  have esqrt : |(NumberField.discr K : ℝ)| ^ (((2 : ℝ) - 1) / 2)
      = Real.sqrt |(NumberField.discr K : ℝ)| := by rw [e1, ← Real.sqrt_eq_rpow]
  have epi : Real.pi ^ (-(d : ℝ) * 2 / 2) = (Real.pi ^ d)⁻¹ := by
    rw [show -(d : ℝ) * 2 / 2 = -(d : ℝ) by ring, Real.rpow_neg hpi.le, Real.rpow_natCast]
  rw [esqrt, epi, eΓ, e1, one_pow, div_one, div_pow]
  ring
end SumProduct
