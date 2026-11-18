-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22110
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:00:11.958514+00:00
-- url     : https://prove2.me/submissions/b945712f-8d5b-428f-8bbd-e123e3739ab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg6151
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5375 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg998

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7611 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5375

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

lemma sg22110_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7611

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22110_oai := @OAI.UniversalTensorSquare.sg22110_oai
