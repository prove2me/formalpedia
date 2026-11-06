-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.exists_binaryCSSSemanticQuantumCodeOfDualLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:30.223522+00:00
-- url     : https://prove2.me/submissions/dc324aba-3ba6-4b11-9ccc-584824980a08

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute

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
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔
        ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
        ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
          toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by
  refine ⟨binaryCSSQuantumCodeOfDualLe xCode zCode hdual, ?_, ?_⟩
  · intro ψ
    exact mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ
  · exact binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute xCode zCode hdual
end QEC.Coding.PauliSymplectic
