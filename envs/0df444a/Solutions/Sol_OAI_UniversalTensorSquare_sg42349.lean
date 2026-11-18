-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42349
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:19:34.98147+00:00
-- url     : https://prove2.me/submissions/f3034ead-2b73-4e0a-8e26-62c0cae5ea1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg2724
import Theorems.Thm_OAI_UniversalTensorSquare_sg3589

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

lemma sg15096 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2724 sg3589

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

lemma sg19138 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1 sg15096

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

lemma sg42349_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19138

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42349_oai := @OAI.UniversalTensorSquare.sg42349_oai
