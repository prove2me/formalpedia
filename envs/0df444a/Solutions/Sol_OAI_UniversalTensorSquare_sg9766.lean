-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg9766
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:07:50.994768+00:00
-- url     : https://prove2.me/submissions/b126e04f-5019-4daf-b593-be86901da693

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1391

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9766_oai : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1391

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg9766_oai := @OAI.UniversalTensorSquare.sg9766_oai
