-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:49:19.207206+00:00
-- url     : https://prove2.me/submissions/1791ff63-19a0-48f4-88ee-6e6a8cf8e80b

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_StabilizerCode_inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_of_inGeneratedGroupUpToSign
import Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_of_not_inBinaryNormalizer

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
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InGeneratedGroupUpToSign E ∨ ¬ Q.1.InBinaryNormalizer E := by
  constructor
  · intro hdet
    by_cases hN : Q.1.InBinaryNormalizer E
    · exact Or.inl
        (inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer Q E hN hdet)
    · exact Or.inr hN
  · rintro (hGenerated | hOutside)
    · exact detectableOn_of_inGeneratedGroupUpToSign Q E hGenerated
    · exact detectableOn_of_not_inBinaryNormalizer Q E hOutside
end QEC.Coding.StabilizerCode
