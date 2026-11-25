-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:23.398969+00:00
-- url     : https://prove2.me/submissions/59fecb73-31d5-4451-9d36-ac83d731ba8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55


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
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError
namespace GroundTheory.Heights₂.Heights.SliceLelongError
theorem _root_.solution :
    Continuous (deriv Real.smoothTransition) ∧ Continuous (deriv (deriv Real.smoothTransition)) := by
  have h1 := contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))
  exact ⟨h1.2.continuous, (contDiff_infty_iff_deriv.mp h1.2).2.continuous⟩
end GroundTheory.Heights₂.Heights.SliceLelongError
