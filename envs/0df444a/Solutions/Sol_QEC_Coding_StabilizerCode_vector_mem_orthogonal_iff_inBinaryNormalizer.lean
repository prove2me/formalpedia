-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.vector_mem_orthogonal_iff_inBinaryNormalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:58:11.459094+00:00
-- url     : https://prove2.me/submissions/6c17eafd-4c9c-4885-90be-5dff4a3a8409

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    E.vector ∈ FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace ↔
      Q.InBinaryNormalizer E := by
  constructor
  · intro hOrth S hS
    apply (commutes_comm E S).2
    exact hOrth S.vector ⟨S, hS, rfl⟩
  · intro hNormalizer _ hvector
    rcases hvector with ⟨S, hS, rfl⟩
    exact (commutes_comm E S).1 (hNormalizer S hS)
end QEC.Coding.StabilizerCode
