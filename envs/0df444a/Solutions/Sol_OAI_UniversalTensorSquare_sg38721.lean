-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38721
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:43:34.20206+00:00
-- url     : https://prove2.me/submissions/6d745ac5-29f9-4a5f-b2f7-a9ef96449284
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg2724
import Theorems.Thm_OAI_UniversalTensorSquare_sg3576

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

lemma sg15075 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2724 sg3576

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

lemma sg19027 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15075

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38721_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19027

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38721_oai := @OAI.UniversalTensorSquare.sg38721_oai
