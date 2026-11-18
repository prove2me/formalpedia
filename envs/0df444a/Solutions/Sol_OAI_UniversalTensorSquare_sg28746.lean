-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28746
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:35:29.438192+00:00
-- url     : https://prove2.me/submissions/c70aeb28-3421-400a-8769-1215403b1dcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1004 : RowSquare [6,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

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

lemma sg6931 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1004

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

lemma sg10345 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6931

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28746_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10345

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28746_oai := @OAI.UniversalTensorSquare.sg28746_oai
