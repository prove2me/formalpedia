-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33966
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:31:06.234204+00:00
-- url     : https://prove2.me/submissions/db8fb519-efe6-46ce-96f4-ac71887d2fdd

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15774
import Theorems.Thm_OAI_UniversalTensorSquare_sg20852

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33966_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15774

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33966_oai := @OAI.UniversalTensorSquare.sg33966_oai
