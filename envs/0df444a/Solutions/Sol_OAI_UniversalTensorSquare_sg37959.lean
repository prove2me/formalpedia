-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37959
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:30:02.39002+00:00
-- url     : https://prove2.me/submissions/5ef38ee5-5366-47dd-8f9e-d8f6d719f3c9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17422
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37959_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,7,7,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17422

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37959_oai := @OAI.UniversalTensorSquare.sg37959_oai
