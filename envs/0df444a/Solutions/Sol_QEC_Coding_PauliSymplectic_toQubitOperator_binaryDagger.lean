-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_binaryDagger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:21.068271+00:00
-- url     : https://prove2.me/submissions/89af1307-cd8b-4f47-98fc-bbb9e47e55c3

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger

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
theorem _root_.solution (P : Binary ι) :
    toQubitOperator (binaryDagger P) = LinearMap.adjoint (toQubitOperator P) :=
  (adjoint_toQubitOperator_eq_binaryDagger P).symm
end QEC.Coding.PauliSymplectic
