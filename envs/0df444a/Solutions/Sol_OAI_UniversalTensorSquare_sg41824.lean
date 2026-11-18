-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41824
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:31:08.477301+00:00
-- url     : https://prove2.me/submissions/ba2712a7-f01f-4e39-8bdc-a9f2ca21dcc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg2724
import Theorems.Thm_OAI_UniversalTensorSquare_sg3581

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15085 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2724 sg3581

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19108 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15085

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41824_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19108

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41824_oai := @OAI.UniversalTensorSquare.sg41824_oai
