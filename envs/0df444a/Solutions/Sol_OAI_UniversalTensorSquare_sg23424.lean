-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23424
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:23:56.543992+00:00
-- url     : https://prove2.me/submissions/43d23eb7-e572-426c-8359-aac0a8d2e434
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg7765

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23424_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7765

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23424_oai := @OAI.UniversalTensorSquare.sg23424_oai
