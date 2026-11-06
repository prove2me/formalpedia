-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.exists_binaryStabilizerCommonFixedQuantumCode_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:12:27.125053+00:00
-- url     : https://prove2.me/submissions/c66d21d9-57a7-4add-b2cd-225cdda060d2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_pairwise_toQubitOperator_commute_of_commutes

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
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔ ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by
  refine ⟨binaryStabilizerCommonFixedQuantumCode S, ?_, ?_⟩
  · intro ψ
    exact mem_binaryStabilizerCommonFixedQuantumCode_carrier (S := S) (ψ := ψ)
  · exact pairwise_toQubitOperator_commute_of_commutes hS
end QEC.Coding.PauliSymplectic
