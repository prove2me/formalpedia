-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33162
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T03:55:59.605235+00:00
-- url     : https://prove2.me/submissions/7589969d-9301-4cb0-9996-b00ebcd5d415
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg19576
import Theorems.Thm_OAI_UniversalTensorSquare_sg3309
import Theorems.Thm_OAI_UniversalTensorSquare_sg892
import Theorems.Thm_OAI_UniversalTensorSquare_sg97

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4468 : RowSquare [9,3,1,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg97 sg892

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

lemma sg19579 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg3309 sg4468

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33162_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19579

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33162_oai := @OAI.UniversalTensorSquare.sg33162_oai
