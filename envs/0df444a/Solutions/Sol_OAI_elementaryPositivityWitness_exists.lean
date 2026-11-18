-- Prove2me | solution 1 for OAI.elementaryPositivityWitness_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:24:56.437208+00:00
-- url     : https://prove2.me/submissions/f7f3eab4-aff3-406d-b7db-79b3ae477224

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom070

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

theorem elementaryPositivityWitness_exists_oai (n : ℕ)
    (G : ElementaryPositivity.NaturalUnitIntervalGraph n) :
    Nonempty G.PermutationWitness :=
  ⟨elementaryPositivityWitness n G⟩

end

end OAI
end

theorem solution : type_of% @OAI.elementaryPositivityWitness_exists_oai := @OAI.elementaryPositivityWitness_exists_oai
