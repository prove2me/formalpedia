-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34268
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:40:31.40944+00:00
-- url     : https://prove2.me/submissions/aa712d36-9403-4ac9-aca7-223dec89b8fe

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17300
import Theorems.Thm_OAI_UniversalTensorSquare_sg20525
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34268_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17300

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34268_oai := @OAI.UniversalTensorSquare.sg34268_oai
