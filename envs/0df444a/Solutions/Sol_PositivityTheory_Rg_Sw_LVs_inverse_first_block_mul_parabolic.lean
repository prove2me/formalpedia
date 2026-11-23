-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inverse_first_block_mul_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:23.50541+00:00
-- url     : https://prove2.me/submissions/c6a4d156-cad4-405b-a01a-a25a8e60af82

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_par

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]
end PositivityTheory.Rg.Sw.LVs
