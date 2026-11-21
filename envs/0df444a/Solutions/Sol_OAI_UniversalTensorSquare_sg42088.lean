-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42088
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:56:21.719052+00:00
-- url     : https://prove2.me/submissions/e2623ea1-88b5-4a1f-8739-e426904edd06

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17754
import Theorems.Thm_OAI_UniversalTensorSquare_sg20523

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

lemma sg42088_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,9,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17754

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42088_oai := @OAI.UniversalTensorSquare.sg42088_oai
