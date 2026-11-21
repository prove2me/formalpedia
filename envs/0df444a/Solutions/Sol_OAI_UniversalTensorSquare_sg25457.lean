-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25457
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:35:28.281021+00:00
-- url     : https://prove2.me/submissions/e064c8f4-f0b0-4a13-b512-a3d277535213

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10250
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

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

lemma sg25457_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10250

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25457_oai := @OAI.UniversalTensorSquare.sg25457_oai
