-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39776
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T14:40:00.625802+00:00
-- url     : https://prove2.me/submissions/3fae4c6b-0ba5-4a46-b08e-8539c28fee51

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18615
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39776_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,8,5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18615

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39776_oai := @OAI.UniversalTensorSquare.sg39776_oai
