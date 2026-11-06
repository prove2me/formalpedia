-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.exists_normalizer_anticommuting_witness_on_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:42:33.548688+00:00
-- url     : https://prove2.me/submissions/522cc0b9-53c6-4a43-8f6c-c4e106367318

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_inBinaryNormalizer_not_commutes
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_nonzero_mem_code

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
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hnotS : ¬ Q.1.InGeneratedGroupUpToSign E) :
    ∃ F ψ,
      Q.1.InBinaryNormalizer F ∧
      ψ ∈ Q.1.code.carrier ∧ ψ ≠ 0 ∧ ¬ Commutes E F := by
  obtain ⟨F, hFN, hNotCommutes⟩ :=
    exists_inBinaryNormalizer_not_commutes Q.1 hN hnotS
  obtain ⟨ψ, hψ, hψne⟩ := exists_nonzero_mem_code Q
  exact ⟨F, ψ, hFN, hψ, hψne, hNotCommutes⟩
end QEC.Coding.StabilizerCode
