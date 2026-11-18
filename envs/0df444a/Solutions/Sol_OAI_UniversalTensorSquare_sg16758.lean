-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg16758
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:12:28.072427+00:00
-- url     : https://prove2.me/submissions/b1f103bb-602b-4f4f-8733-4b2deedf797c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3687
import Theorems.Thm_OAI_UniversalTensorSquare_sg4083

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16758_oai : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3687 sg4083

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg16758_oai := @OAI.UniversalTensorSquare.sg16758_oai
