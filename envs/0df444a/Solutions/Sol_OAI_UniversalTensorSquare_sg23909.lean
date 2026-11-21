-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23909
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:48:48.207938+00:00
-- url     : https://prove2.me/submissions/229f2e99-2895-4f56-b421-e61e8ce9fb36

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12619
import Theorems.Thm_OAI_UniversalTensorSquare_sg5533

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23909_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg5533 sg12619

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23909_oai := @OAI.UniversalTensorSquare.sg23909_oai
