-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_rigSymFormTauI_isBasisOf_a1e28445b82a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:40.99081+00:00
-- url     : https://prove2.me/submissions/65ca3c1e-fc49-48f9-b488-0a84a8f7349d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeFam_linearIndependent_5353412cd3cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeFam_span_21c22d7a9007
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeSec_mem_8f4fbee0788e


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
    rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam :=
  ⟨fun i => thetaThreeSec_mem i, thetaThreeFam_linearIndependent, thetaThreeFam_span⟩
end GroundTheory.Heights₂.Heights.KeyFormula
