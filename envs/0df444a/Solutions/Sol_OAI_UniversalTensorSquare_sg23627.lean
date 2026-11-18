-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23627
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:52:20.78554+00:00
-- url     : https://prove2.me/submissions/d0fea6b5-4e47-4c06-8900-c9bafd307ec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6891
import Theorems.Thm_OAI_UniversalTensorSquare_sg8718

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

lemma sg23627_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6891 sg8718

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23627_oai := @OAI.UniversalTensorSquare.sg23627_oai
