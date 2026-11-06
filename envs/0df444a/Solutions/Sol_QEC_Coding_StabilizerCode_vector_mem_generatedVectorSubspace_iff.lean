-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.vector_mem_generatedVectorSubspace_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:43:48.305223+00:00
-- url     : https://prove2.me/submissions/ec35b4b7-a358-4600-a485-de8a3a27c6ef

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability

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
    E.vector ∈ Q.generatedVectorSubspace ↔ Q.InGeneratedGroupUpToSign E := by
  constructor
  · rintro ⟨S, hS, hvector⟩
    exact ⟨S, hS, hvector.symm⟩
  · rintro ⟨S, hS, hvector⟩
    exact ⟨S, hS, hvector.symm⟩
end QEC.Coding.StabilizerCode
