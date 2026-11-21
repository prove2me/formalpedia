-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42563
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:34:42.952209+00:00
-- url     : https://prove2.me/submissions/74c229ef-20a0-44fe-81c4-df31f4f1b71b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg20146

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42563_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,12,6,6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20146

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42563_oai := @OAI.UniversalTensorSquare.sg42563_oai
