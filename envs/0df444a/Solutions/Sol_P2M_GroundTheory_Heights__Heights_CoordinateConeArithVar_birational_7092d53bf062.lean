-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_birational_7092d53bf062
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:42.855059+00:00
-- url     : https://prove2.me/submissions/1b9d302a-3600-46e4-b868-a794d737ad70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_coe_aeval_ratioPtL_ffa96add92ff

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Birational (ratioPtL y c) := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc s.2
  refine ⟨d, g, h, hg, hh, fun h0 ↦ n ?_, Subtype.ext ?_⟩
  · rw [← coe_aeval_ratioPtL, h0]
    rfl
  · rw [coe_aeval_ratioPtL, IntermediateField.coe_mul, coe_aeval_ratioPtL, e]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
