-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37030
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T12:29:02.06886+00:00
-- url     : https://prove2.me/submissions/38dd4cef-82b6-40b7-8ed0-fca4700113f2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg19576
import Theorems.Thm_OAI_UniversalTensorSquare_sg3581
import Theorems.Thm_OAI_UniversalTensorSquare_sg4158
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19592 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3581 sg4158

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 91. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37030_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,8,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19592

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37030_oai := @OAI.UniversalTensorSquare.sg37030_oai
