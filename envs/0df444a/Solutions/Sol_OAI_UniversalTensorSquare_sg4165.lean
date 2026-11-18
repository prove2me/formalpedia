-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4165
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:25:28.207848+00:00
-- url     : https://prove2.me/submissions/2f0eff16-a8a6-47cd-9711-4fd1926ba7b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg236
import Theorems.Thm_OAI_UniversalTensorSquare_sg396

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4165_oai : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg236

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4165_oai := @OAI.UniversalTensorSquare.sg4165_oai
