-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_intVec_one_081da4c52f7a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:05.696824+00:00
-- url     : https://prove2.me/submissions/12561414-48d6-4c2a-ad20-ad180f275369

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial

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
open Complex Matrix Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (v : Fin 1 → ℤ) : intVec v 0 = (v 0 : ℂ) := rfl
end GroundTheory.Heights₂.Heights.KeyFormula
