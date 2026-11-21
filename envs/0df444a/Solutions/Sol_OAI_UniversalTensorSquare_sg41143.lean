-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41143
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T16:28:29.87693+00:00
-- url     : https://prove2.me/submissions/8c855837-e4a3-4490-ab0e-afc54106d0ef

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg8067
import Theorems.Thm_OAI_UniversalTensorSquare_sg840
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18759 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg840 sg8067

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 101. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41143_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,8,8,7,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18759

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41143_oai := @OAI.UniversalTensorSquare.sg41143_oai
