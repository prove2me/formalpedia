-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21731
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:46:33.794499+00:00
-- url     : https://prove2.me/submissions/b94dcc16-fb94-4561-924a-f3f1b9e06dd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg587
import Theorems.Thm_OAI_UniversalTensorSquare_sg6768
import Theorems.Thm_OAI_UniversalTensorSquare_sg808

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

lemma sg6425 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg808

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21731_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6425 sg6768

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21731_oai := @OAI.UniversalTensorSquare.sg21731_oai
