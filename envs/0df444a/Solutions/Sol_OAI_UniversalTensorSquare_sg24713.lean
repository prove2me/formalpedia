-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24713
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:05:44.449193+00:00
-- url     : https://prove2.me/submissions/703fbcb3-db34-4f2f-b1a0-5079d941a52c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10236
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24713_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8430 sg10236

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24713_oai := @OAI.UniversalTensorSquare.sg24713_oai
