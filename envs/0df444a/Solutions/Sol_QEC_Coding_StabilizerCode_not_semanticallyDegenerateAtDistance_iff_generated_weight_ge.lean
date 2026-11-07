-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:15.075066+00:00
-- url     : https://prove2.me/submissions/9f007612-be0c-48bf-a062-7d853d5f5bb9

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Theorems.Thm_QEC_Coding_StabilizerCode_semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign

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
    (Q : SourceValidBinary ι) (d : Nat)
    (hd : SemanticStabilizerDistance Q d) :
    ¬ SemanticallyDegenerateAtDistance Q d ↔
      ∀ E, Q.1.InGeneratedGroupUpToSign E →
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) →
        d ≤ weight E := by
  constructor
  · intro hNondegenerate E hGenerated hNonidentity
    apply Nat.le_of_not_gt
    intro hWeight
    apply hNondegenerate
    exact
      (semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign Q d).2
        ⟨hd, E, hGenerated, hNonidentity, hWeight⟩
  · intro hWeight hDegenerate
    obtain ⟨_, E, hGenerated, hNonidentity, hLowWeight⟩ :=
      (semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign Q d).1
        hDegenerate
    exact (Nat.not_lt_of_ge (hWeight E hGenerated hNonidentity)) hLowWeight
end QEC.Coding.StabilizerCode
