-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedErrorOperators_adjoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:59.724561+00:00
-- url     : https://prove2.me/submissions/4a921f84-6f85-4750-9387-a71da478b807

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedByWeight_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedErrorOperators_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryDagger

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
theorem _root_.solution {B : Nat}
    {E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)}
    (hE : E ∈ scopedErrorOperators (ι := ι) B) :
    LinearMap.adjoint E ∈ scopedErrorOperators (ι := ι) B := by
  rw [mem_scopedErrorOperators_iff] at hE ⊢
  rcases hE with ⟨P, hP, rfl⟩
  exact ⟨binaryDagger P, mem_scopedByWeight_binaryDagger hP, toQubitOperator_binaryDagger P⟩
end QEC.Coding.PauliSymplectic
