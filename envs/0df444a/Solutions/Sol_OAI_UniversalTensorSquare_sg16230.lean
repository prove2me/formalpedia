-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg16230
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:21:01.116654+00:00
-- url     : https://prove2.me/submissions/7dfe8780-cebc-46cf-b16d-fa2ba2c77ed5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3553
import Theorems.Thm_OAI_UniversalTensorSquare_sg4319

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16230_oai : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3553 sg4319

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg16230_oai := @OAI.UniversalTensorSquare.sg16230_oai
