-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25455
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:50:16.44891+00:00
-- url     : https://prove2.me/submissions/cd929374-6cec-4086-afd9-854bc77492f0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10264
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25455_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10264

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25455_oai := @OAI.UniversalTensorSquare.sg25455_oai
