-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_formSec_X_zero_25b6e5472f1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:30.961139+00:00
-- url     : https://prove2.me/submissions/914f5618-d68e-42c3-b011-87e7661d276a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf

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
    rigSymFormTauI.formSec (r := 2) thetaThreeFam (MvPolynomial.X 0) = thetaThreeSec 0 := by
  funext z
  simp [RigSymForm.formSec, thetaThreeFam]
end GroundTheory.Heights₂.Heights.KeyFormula
