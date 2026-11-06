-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:59:57.958971+00:00
-- url     : https://prove2.me/submissions/5c48e7ab-2986-481f-8f03-8e571ce699e0

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) (E : Binary ι) :
    ¬ Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InBinaryNormalizer E ∧ ¬ Q.1.InGeneratedGroupUpToSign E := by
  rw [detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer]
  tauto
end QEC.Coding.StabilizerCode
