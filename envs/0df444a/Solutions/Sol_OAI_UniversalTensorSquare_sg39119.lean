-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39119
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:54:43.637601+00:00
-- url     : https://prove2.me/submissions/b3bf09d1-0514-4bc3-bc31-70787677762e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18070
import Theorems.Thm_OAI_UniversalTensorSquare_sg20498
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 96. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39119_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,7,7,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18070

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39119_oai := @OAI.UniversalTensorSquare.sg39119_oai
