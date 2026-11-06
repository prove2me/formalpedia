-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.generatedVectorSubspace_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:29:36.896953+00:00
-- url     : https://prove2.me/submissions/cd4b95dd-234a-47e3-bec1-c1b85051425a

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedGroup_pairwise_commutes

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
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Q.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨R, hR, rfl⟩
  change FiniteSymplectic.form R.vector P.vector = 0
  exact (commutes_comm P R).1 (generatedGroup_pairwise_commutes Q hP hR)
end QEC.Coding.StabilizerCode
