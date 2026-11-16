-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_positive32
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:53:57.485982+00:00
-- url     : https://prove2.me/submissions/7fab2533-eca8-4045-bd22-69a1e0419634

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

lemma certificate32 : contractionInteger [3,1,1] [3,1,1] [3,2]
    (Equiv.refl (Fin 5)) hookPlacement (Equiv.refl (Fin 5)) flag32 = -4 := by decide +kernel

noncomputable section

lemma five_positive32_oai :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols [3,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply five_positive_certificate [3,2] (by decide) (by simp) rfl
    hookPlacement (Equiv.refl _) flag32
  intro hz
  have hz' : (-4 : ℤ) = 0 := certificate32.symm.trans hz
  norm_num at hz'

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_positive32_oai := @OAI.UniversalTensorSquare.five_positive32_oai
