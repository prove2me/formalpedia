-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38930
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:01:25.857825+00:00
-- url     : https://prove2.me/submissions/2ebcddb9-5014-46b8-add2-1c0b0f3a252b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16165
import Theorems.Thm_OAI_UniversalTensorSquare_sg20814

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

lemma sg38930_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20814 sg16165

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38930_oai := @OAI.UniversalTensorSquare.sg38930_oai
