-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19211
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:13:19.893424+00:00
-- url     : https://prove2.me/submissions/a2432bea-9159-4dde-ba19-eed1c36a2677

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg14236

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19211_oai : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14236

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19211_oai := @OAI.UniversalTensorSquare.sg19211_oai
