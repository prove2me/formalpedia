-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_vanishingCech_hyps_744f01426a4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:00:36.069905+00:00
-- url     : https://prove2.me/submissions/1230b066-869a-4092-8d14-266ba93d865b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_rigSymFormTauI_isBasisOf_a1e28445b82a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution :
    rigSymFormTauI.g = 1 ∧ 3 ≤ 3 ∧ rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam ∧ 1 ≤ 1 ∧
      rigSymFormTauI.IsCocycle 3 1 (0 + 1) thetaThreeFam (fun _ _ => 0) := by
  refine ⟨rfl, le_rfl, rigSymFormTauI_isBasisOf, le_rfl, ?_, ?_⟩
  · intro J _
    exact ⟨0, 0, Submodule.zero_mem _, fun z _ => by simp⟩
  · intro J _ z _
    simp [cechD]
end GroundTheory.Heights₂.Heights.KeyFormula
