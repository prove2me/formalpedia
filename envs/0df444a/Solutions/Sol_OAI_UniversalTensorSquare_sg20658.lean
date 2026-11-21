-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20658
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:31:58.856711+00:00
-- url     : https://prove2.me/submissions/b6668d1a-46d1-49a4-8b4f-8ad0292eace4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3258
import Theorems.Thm_OAI_UniversalTensorSquare_sg4352

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20658_oai : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4352

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20658_oai := @OAI.UniversalTensorSquare.sg20658_oai
