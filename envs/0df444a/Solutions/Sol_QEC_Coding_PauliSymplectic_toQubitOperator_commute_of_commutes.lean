-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:36.130875+00:00
-- url     : https://prove2.me/submissions/ea43bb18-b060-4aa8-890d-43222534d01f

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_of_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_binarySwapPhase_eq

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
theorem _root_.solution (P Q : Binary ι) (h : Commutes P Q) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  toQubitOperator_commute_of_binarySwapPhase_eq P Q
    (binarySwapPhase_eq_of_commutes P Q h)
end QEC.Coding.PauliSymplectic
