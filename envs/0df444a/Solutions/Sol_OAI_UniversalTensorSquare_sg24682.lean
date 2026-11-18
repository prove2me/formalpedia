-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24682
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:33:46.560144+00:00
-- url     : https://prove2.me/submissions/3fa62c7c-628d-4158-801f-da786f1e8eae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg262
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1765 : RowSquare [6,2,1,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg262

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

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

lemma sg9737 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1765

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24682_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9737

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24682_oai := @OAI.UniversalTensorSquare.sg24682_oai
