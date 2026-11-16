-- Prove2me | solution 1 for OAI.UniversalTensorSquare.five_positive_target_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:52:36.098337+00:00
-- url     : https://prove2.me/submissions/5ea0eff7-b5f2-488e-9cd5-34314a712921

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US012

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

lemma five_positive_target_eq_oai {μ ν : YoungDiagram} (hμ : μ.card = 5) (hν : ν.card = 5)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.five_positive_target_eq_oai := @OAI.UniversalTensorSquare.five_positive_target_eq_oai
