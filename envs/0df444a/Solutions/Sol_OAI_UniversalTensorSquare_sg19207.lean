-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19207
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:13:16.251659+00:00
-- url     : https://prove2.me/submissions/34c0b9d0-0130-44d1-8cb8-4d45b2ff94e5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg14232

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

lemma sg19207_oai : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14232

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19207_oai := @OAI.UniversalTensorSquare.sg19207_oai
