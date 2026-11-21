-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42026
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T18:23:30.735494+00:00
-- url     : https://prove2.me/submissions/cf2692ce-5f37-45b3-a88a-026c13fb2531

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18098
import Theorems.Thm_OAI_UniversalTensorSquare_sg20498
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42026_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18098

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42026_oai := @OAI.UniversalTensorSquare.sg42026_oai
