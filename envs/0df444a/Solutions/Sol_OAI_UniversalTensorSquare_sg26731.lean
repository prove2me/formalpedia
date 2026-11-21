-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26731
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:15:19.287046+00:00
-- url     : https://prove2.me/submissions/dff5833c-e031-4878-b939-13ed89efc4f0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg1377
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721

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

lemma sg8202 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1377

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9566 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8202

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26731_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9566

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26731_oai := @OAI.UniversalTensorSquare.sg26731_oai
