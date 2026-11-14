-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21806
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:32:00.444104+00:00
-- url     : https://prove2.me/submissions/8635c08d-5619-4abb-b95e-6a4c2b7d2027
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6418
import Theorems.Thm_OAI_UniversalTensorSquare_sg6780

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

lemma sg21806_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6418 sg6780

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21806_oai := @OAI.UniversalTensorSquare.sg21806_oai
