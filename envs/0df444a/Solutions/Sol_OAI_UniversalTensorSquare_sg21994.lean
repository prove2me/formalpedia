-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21994
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:57:43.251051+00:00
-- url     : https://prove2.me/submissions/dc8faa0d-b969-449e-9fde-c182c8eb80b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg890
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg6296 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg910

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

lemma sg7361 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg890 sg1041

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

lemma sg21994_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7361

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21994_oai := @OAI.UniversalTensorSquare.sg21994_oai
