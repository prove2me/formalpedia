-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21773
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:31:21.744204+00:00
-- url     : https://prove2.me/submissions/ce54c551-06e1-4e29-ba81-18bcd7d2c10f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6418
import Theorems.Thm_OAI_UniversalTensorSquare_sg6771

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

lemma sg21773_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg6418 sg6771

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21773_oai := @OAI.UniversalTensorSquare.sg21773_oai
