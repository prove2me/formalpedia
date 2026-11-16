-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_positive41
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:54:00.554324+00:00
-- url     : https://prove2.me/submissions/1676152c-35d7-4cc1-8415-378945b22e23

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US012
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

lemma certificate41 : contractionInteger [3,1,1] [3,1,1] [4,1]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag41 = 2 := by decide +kernel

noncomputable section

lemma five_positive41_oai :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [4,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [4,1] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag41
  intro hz
  have hz' : (2 : ℤ) = 0 := certificate41.symm.trans hz
  norm_num at hz'

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_positive41_oai := @OAI.UniversalTensorSquare.five_positive41_oai
