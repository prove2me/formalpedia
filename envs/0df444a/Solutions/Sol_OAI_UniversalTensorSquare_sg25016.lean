-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25016
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:49:51.516683+00:00
-- url     : https://prove2.me/submissions/2350170f-ba45-41d6-a31e-a5b502c42ad5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10242
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25016_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10242

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25016_oai := @OAI.UniversalTensorSquare.sg25016_oai
