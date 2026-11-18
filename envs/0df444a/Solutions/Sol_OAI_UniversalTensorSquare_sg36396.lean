-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36396
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:05:05.439208+00:00
-- url     : https://prove2.me/submissions/dada637d-53de-4b14-920d-be9f47918ed8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18418
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36396_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,6,6,6,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18418

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36396_oai := @OAI.UniversalTensorSquare.sg36396_oai
