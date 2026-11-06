-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:28.839064+00:00
-- url     : https://prove2.me/submissions/190dde1c-41e5-45ff-ab84-4e6084656ce3

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_symplecticForm_eq_zero
import Theorems.Thm_QEC_Coding_LinearCode_symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual


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
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact cssXCheck_toQubitOperator_commute_cssZCheck_of_symplecticForm_eq_zero
    (LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz)
end QEC.Coding.PauliSymplectic
