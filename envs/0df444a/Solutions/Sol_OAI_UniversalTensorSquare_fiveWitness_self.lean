-- Prove2me | solution 1 for OAI.UniversalTensorSquare.fiveWitness_self
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:22.899147+00:00
-- url     : https://prove2.me/submissions/3a661363-24ba-46ac-9091-769216235097

import Mathlib
import Definitions.Def_OAIQ259US002

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

namespace UniversalTensorSquare

lemma fiveWitness_self_oai : fiveWitness.transpose = fiveWitness := by
  apply YoungDiagram.ext
  decide

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.fiveWitness_self_oai := @OAI.UniversalTensorSquare.fiveWitness_self_oai
