-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_height_standard_eq_blockSum_e27d47607e91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:27.766269+00:00
-- url     : https://prove2.me/submissions/8559905d-5fc0-4066-a5fa-86ffb04537d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockNonzero_sigma_8db15361a0fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    height (HermLine.standard n) x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      ∑ k, blockSum (coordVec x) k := by
  rw [height_eq_blockSum _ x hx]
  have h0 : ∀ σ : coordField x →+* ℂ,
      metricDefect (HermLine.standard n) (fun k i ↦ σ (coordVec x k i)) = 0 :=
    fun σ ↦ metricDefect_standard _ (blockNonzero_sigma hx σ)
  simp only [h0, Finset.sum_const_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  change ((1 : ℤ) : ℝ) * _ = _
  rw [Int.cast_one, one_mul]
end GroundTheory.Heights₂.Heights
