-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23457
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:26:55.645496+00:00
-- url     : https://prove2.me/submissions/3e3481c8-3abf-4cd2-a0c6-d46e9c7f3b4c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6150
import Theorems.Thm_OAI_UniversalTensorSquare_sg7703

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23457_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7703

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23457_oai := @OAI.UniversalTensorSquare.sg23457_oai
