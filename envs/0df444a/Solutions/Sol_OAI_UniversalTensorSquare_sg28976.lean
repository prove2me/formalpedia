-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28976
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:40:27.047959+00:00
-- url     : https://prove2.me/submissions/155e567c-aaa1-4e15-a838-25e76b9b4eba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1002
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6924 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg999

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10331 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6924

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28976_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10331

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28976_oai := @OAI.UniversalTensorSquare.sg28976_oai
