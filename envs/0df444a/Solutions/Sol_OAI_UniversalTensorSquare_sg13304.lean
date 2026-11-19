-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13304
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:04:19.995112+00:00
-- url     : https://prove2.me/submissions/0fd5330f-2312-47d0-a934-a26477682d36

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1637
import Theorems.Thm_OAI_UniversalTensorSquare_sg2552

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13304_oai : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2552

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13304_oai := @OAI.UniversalTensorSquare.sg13304_oai
