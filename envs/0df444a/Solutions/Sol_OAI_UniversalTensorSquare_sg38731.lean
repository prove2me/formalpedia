-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38731
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:43:50.513595+00:00
-- url     : https://prove2.me/submissions/f4a9bf1d-8196-469c-9341-aef93384e87b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17448
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38731_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17448

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38731_oai := @OAI.UniversalTensorSquare.sg38731_oai
