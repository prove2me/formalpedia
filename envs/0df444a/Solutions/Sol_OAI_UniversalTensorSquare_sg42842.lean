-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42842
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:50:27.727382+00:00
-- url     : https://prove2.me/submissions/3fc181b9-beb8-4217-94f6-3d887f9762cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1332
import Theorems.Thm_OAI_UniversalTensorSquare_sg15608
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3683 : RowSquare [9,2,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19 sg1332

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg15148 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2633 sg3683

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

lemma sg19545 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15148

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42842_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,7,7,7,7,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19545

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42842_oai := @OAI.UniversalTensorSquare.sg42842_oai
