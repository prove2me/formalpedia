-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29239
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:34:23.719202+00:00
-- url     : https://prove2.me/submissions/7f886696-8f39-4769-b4ca-1c8146438479
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg137
import Theorems.Thm_OAI_UniversalTensorSquare_sg4161
import Theorems.Thm_OAI_UniversalTensorSquare_sg6907

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

lemma sg11480 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg4161

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29239_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6907 sg11480

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29239_oai := @OAI.UniversalTensorSquare.sg29239_oai
