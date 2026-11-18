-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42091
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:56:25.833163+00:00
-- url     : https://prove2.me/submissions/78edf49e-eabc-4701-88bc-95e91cbed8ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11748
import Theorems.Thm_OAI_UniversalTensorSquare_sg151
import Theorems.Thm_OAI_UniversalTensorSquare_sg16165

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20840 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg151 sg11748

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

lemma sg42091_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,5,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20840 sg16165

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42091_oai := @OAI.UniversalTensorSquare.sg42091_oai
