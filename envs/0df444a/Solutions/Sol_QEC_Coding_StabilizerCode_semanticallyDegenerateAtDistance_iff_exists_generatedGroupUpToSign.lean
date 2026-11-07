-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:24.621985+00:00
-- url     : https://prove2.me/submissions/fbccb7a4-6337-4efb-971c-8288c83afc06

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Theorems.Thm_QEC_Coding_StabilizerCode_inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar

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
    SemanticallyDegenerateAtDistance Q d ↔
      SemanticStabilizerDistance Q d ∧
      ∃ E : Binary ι,
        Q.1.InGeneratedGroupUpToSign E ∧
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) ∧
        weight E < d := by
  constructor
  · rintro ⟨hd, E, c, hNonidentity, hWeight, hc, hScalar⟩
    refine ⟨hd, E, ?_, hNonidentity, hWeight⟩
    exact
      (inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar Q E).2
        ⟨c, hc, hScalar⟩
  · rintro ⟨hd, E, hGenerated, hNonidentity, hWeight⟩
    obtain ⟨c, hc, hScalar⟩ :=
      (inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar Q E).1
        hGenerated
    exact ⟨hd, E, c, hNonidentity, hWeight, hc, hScalar⟩
end QEC.Coding.StabilizerCode
