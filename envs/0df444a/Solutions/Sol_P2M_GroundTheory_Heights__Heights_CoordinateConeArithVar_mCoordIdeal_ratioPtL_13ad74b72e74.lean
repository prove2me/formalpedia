-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPtL_13ad74b72e74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:50.718126+00:00
-- url     : https://prove2.me/submissions/b2bd20fe-38eb-48f0-8ace-7de5be0a2c26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_ratioPt_f0fad8b56985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_mCoordIdeal_comp_3d3b4b1e6c7d

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
theorem _root_.solution [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : mCoordIdeal (ratioPtL y c) = mCoordIdeal y := by
  rw [mCoordIdeal_ratioPt y c hc, ← mCoordIdeal_comp (algebraMap (ratioField y c) Ω)]
  rfl
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
