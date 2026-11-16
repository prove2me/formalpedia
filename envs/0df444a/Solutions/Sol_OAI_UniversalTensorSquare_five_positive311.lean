-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_positive311
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:52:27.91921+00:00
-- url     : https://prove2.me/submissions/ce8b1aee-1f63-45e1-bc5f-4a7c0d24c946

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

lemma certificate311 : contractionInteger [3,1,1] [3,1,1] [3,1,1]
    (Equiv.refl (Fin 5)) (Equiv.swap (2 : Fin 5) 3) (Equiv.swap (1 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3) flag311 = 4 := by
  decide +kernel

noncomputable section

lemma five_positive311_oai :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) := by
  apply five_positive_certificate [3,1,1] (by decide) (by simp) rfl
    (Equiv.swap 2 3) (Equiv.swap 1 2 * Equiv.swap 1 3) flag311
  intro hz
  have hz' : (4 : ℤ) = 0 := certificate311.symm.trans hz
  norm_num at hz'

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_positive311_oai := @OAI.UniversalTensorSquare.five_positive311_oai
