-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19620
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:13:23.40052+00:00
-- url     : https://prove2.me/submissions/1ee57db0-544c-465e-a3ef-345c308b974f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg14319

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19620_oai : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14319

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19620_oai := @OAI.UniversalTensorSquare.sg19620_oai
