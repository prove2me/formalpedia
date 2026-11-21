-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39052
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:51:01.277201+00:00
-- url     : https://prove2.me/submissions/47003923-9dea-4081-85c6-c44ec05675d5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18069
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

lemma sg39052_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,7,6,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18069

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39052_oai := @OAI.UniversalTensorSquare.sg39052_oai
