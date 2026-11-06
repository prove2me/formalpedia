-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_dual_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:08:19.580406+00:00
-- url     : https://prove2.me/submissions/6a6bdee9-2d7a-487c-b29e-caabb4d1aba4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual xCode hx (hdual hz)
end QEC.Coding.PauliSymplectic
