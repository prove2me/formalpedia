-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.mem_scopedErrorOperators_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:21:47.258207+00:00
-- url     : https://prove2.me/submissions/5d2b2036-5de6-4385-ab5a-8eb45327460e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics

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
theorem _root_.solution (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ scopedErrorOperators (ι := ι) B ↔
      ∃ P : Binary ι, P ∈ scopedByWeight (ι := ι) B ∧ toQubitOperator P = E := by
  rfl
end QEC.Coding.PauliSymplectic
