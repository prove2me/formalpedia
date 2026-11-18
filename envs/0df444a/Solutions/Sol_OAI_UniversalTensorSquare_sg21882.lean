-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21882
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:49:30.666305+00:00
-- url     : https://prove2.me/submissions/2f1808c5-8086-4052-9f65-322ab61f69ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg587
import Theorems.Thm_OAI_UniversalTensorSquare_sg808

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6425 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg808

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg6782 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1416

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21882_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6425 sg6782

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21882_oai := @OAI.UniversalTensorSquare.sg21882_oai
