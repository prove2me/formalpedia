-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37821
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T12:52:24.304999+00:00
-- url     : https://prove2.me/submissions/30d802b5-d4ce-42f9-9f89-524658020578

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg8043
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18502 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8043

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37821_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,6,6,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18502

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37821_oai := @OAI.UniversalTensorSquare.sg37821_oai
