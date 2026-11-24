-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_joint_theorem_A__e6b3bc7ee1c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:19.436642+00:00
-- url     : https://prove2.me/submissions/df86ee52-5f27-482d-8547-284bd2ca2867

import Definitions.Def_Formalism_HermitianCurvature_StatementK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_K_jointTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
end Formalism.FourierDecayAlt.P
