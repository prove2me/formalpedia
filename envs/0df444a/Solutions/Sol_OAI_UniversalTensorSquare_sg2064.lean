-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2064
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:52:19.286495+00:00
-- url     : https://prove2.me/submissions/77f9a515-cf32-44ff-a94f-c8605a6dccd1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2064_oai : RowSquare [4,3,1,1,1,1,1,1] [5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2064_oai := @OAI.UniversalTensorSquare.sg2064_oai
