-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42022
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:55:35.588594+00:00
-- url     : https://prove2.me/submissions/4981e1a1-d9fd-4c75-bec8-78006cff3c87

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16409
import Theorems.Thm_OAI_UniversalTensorSquare_sg20719

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

lemma sg42022_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20719 sg16409

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42022_oai := @OAI.UniversalTensorSquare.sg42022_oai
