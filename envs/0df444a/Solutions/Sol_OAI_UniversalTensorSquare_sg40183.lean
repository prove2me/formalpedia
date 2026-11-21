-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40183
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T15:11:44.581662+00:00
-- url     : https://prove2.me/submissions/50a67d24-3e4d-4b67-9f8c-da8967a1d507

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18081
import Theorems.Thm_OAI_UniversalTensorSquare_sg20498
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 99. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40183_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,12,7,7,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18081

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40183_oai := @OAI.UniversalTensorSquare.sg40183_oai
