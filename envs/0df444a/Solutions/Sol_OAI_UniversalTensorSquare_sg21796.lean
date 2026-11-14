-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21796
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:31:47.7652+00:00
-- url     : https://prove2.me/submissions/1f16230c-60c3-4509-b14d-19d75cf5e321
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6162
import Theorems.Thm_OAI_UniversalTensorSquare_sg7528

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

lemma sg21796_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg6162 sg7528

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21796_oai := @OAI.UniversalTensorSquare.sg21796_oai
