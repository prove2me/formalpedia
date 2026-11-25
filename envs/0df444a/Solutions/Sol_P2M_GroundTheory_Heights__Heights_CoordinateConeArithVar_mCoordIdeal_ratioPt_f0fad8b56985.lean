-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:09.014433+00:00
-- url     : https://prove2.me/submissions/e2713dca-3836-4e74-b904-a024737bff45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_scaleT_inv_cd75bf8c9ee9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mConeMap_eq_scale_ee6593a6f5ce

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
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    mCoordIdeal y = mCoordIdeal (ratioPt y c) := by
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_eq_scale y c hc]
  constructor
  · intro h
    have h2 := congrArg (scaleT fun k ↦ (y ⟨k, c k⟩)⁻¹) h
    rwa [scaleT_inv _ hc, map_zero] at h2
  · intro h
    rw [h, map_zero]
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
