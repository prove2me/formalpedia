-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_positive5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:36:48.224196+00:00
-- url     : https://prove2.me/submissions/68211e78-8f6b-4547-a468-b9c76e48000b

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_certificate5
import Theorems.Thm_OAI_UniversalTensorSquare_five_positive_certificate

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

lemma five_positive5_oai :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [5] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [5] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag5
  intro hz
  have hz' : (20 : ℤ) = 0 := certificate5.symm.trans hz
  norm_num at hz'

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_positive5_oai := @OAI.UniversalTensorSquare.five_positive5_oai
