-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28390
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:33:20.378002+00:00
-- url     : https://prove2.me/submissions/6cf5c071-6f93-4681-a329-833a4f25c024

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10428
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8414 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2626

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28390_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10428

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28390_oai := @OAI.UniversalTensorSquare.sg28390_oai
