-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:03:48.283853+00:00
-- url     : https://prove2.me/submissions/0c9f1c8c-6cb9-4856-bced-e76b77e475f0

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Theorems.Thm_QEC_Coding_StabilizerCode_not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign

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
    (Q : SourceValidBinary ι) (d : Nat) :
    SemanticStabilizerDistance Q d ↔
      ∃ E : Binary ι,
        Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E ∧
        weight E = d ∧
        ∀ F : Binary ι,
          Q.1.InBinaryNormalizer F →
          ¬ Q.1.InGeneratedGroupUpToSign F →
          d ≤ weight F := by
  constructor
  · rintro ⟨E, hNondetectable, hWeight, hLeast⟩
    have hLogical :=
      (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q E).1 hNondetectable
    refine ⟨E, hLogical.1, hLogical.2, hWeight, ?_⟩
    intro F hNormalizer hOutsideGenerated
    exact hLeast F
      ((not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q F).2 ⟨hNormalizer, hOutsideGenerated⟩)
  · rintro ⟨E, hNormalizer, hOutsideGenerated, hWeight, hLeast⟩
    refine ⟨E, ?_, hWeight, ?_⟩
    · exact
        (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
          Q E).2 ⟨hNormalizer, hOutsideGenerated⟩
    · intro F hNondetectable
      have hLogical :=
        (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
          Q F).1 hNondetectable
      exact hLeast F hLogical.1 hLogical.2
end QEC.Coding.StabilizerCode
