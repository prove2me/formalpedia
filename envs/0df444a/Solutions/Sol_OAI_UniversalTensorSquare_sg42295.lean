-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42295
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:12:35.114197+00:00
-- url     : https://prove2.me/submissions/efe7c3ce-5baf-4bcd-8d9f-32acc2d69be8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg15608
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg2407

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1527 : RowSquare [7,2,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg180

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11685 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg1527 sg2407

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg19507 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg165 sg11685

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 104. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42295_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19507

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42295_oai := @OAI.UniversalTensorSquare.sg42295_oai
