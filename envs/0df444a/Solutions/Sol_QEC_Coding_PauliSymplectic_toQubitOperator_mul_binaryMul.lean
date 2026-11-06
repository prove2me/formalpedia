-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_mul_binaryMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:58.234974+00:00
-- url     : https://prove2.me/submissions/41e06cdb-6d4c-4487-88bc-ee19ebc665b5

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul

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
theorem _root_.solution (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator (binaryMul P Q) :=
  (toQubitOperator_binaryMul P Q).symm
end QEC.Coding.PauliSymplectic
