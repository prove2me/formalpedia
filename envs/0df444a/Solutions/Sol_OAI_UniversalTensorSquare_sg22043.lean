-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg22043
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T03:38:22.737379+00:00
-- url     : https://prove2.me/submissions/6353ee1b-27de-49c4-9f9e-e255bef9aeab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6315
import Theorems.Thm_OAI_UniversalTensorSquare_sg7310

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

lemma sg22043_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7310

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg22043_oai := @OAI.UniversalTensorSquare.sg22043_oai
