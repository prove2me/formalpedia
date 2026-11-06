-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedErrorOperators_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:59.038976+00:00
-- url     : https://prove2.me/submissions/0e0aeaae-7a9b-4d4b-9dcd-a672fd25a521

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedByWeight_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_mem_scopedErrorOperators_iff
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
theorem _root_.solution {B C : Nat}
    {E F : Semantics.Operator (Semantics.Qubit.QubitRegister ι)}
    (hE : E ∈ scopedErrorOperators (ι := ι) B)
    (hF : F ∈ scopedErrorOperators (ι := ι) C) :
    E * F ∈ scopedErrorOperators (ι := ι) (B + C) := by
  rw [mem_scopedErrorOperators_iff] at hE hF ⊢
  rcases hE with ⟨P, hP, rfl⟩
  rcases hF with ⟨Q, hQ, rfl⟩
  exact ⟨binaryMul P Q, mem_scopedByWeight_binaryMul hP hQ, toQubitOperator_binaryMul P Q⟩
end QEC.Coding.PauliSymplectic
