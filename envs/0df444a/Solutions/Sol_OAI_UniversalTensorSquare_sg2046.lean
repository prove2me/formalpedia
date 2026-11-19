-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2046
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:49:10.038019+00:00
-- url     : https://prove2.me/submissions/894237e9-76e4-4d28-9cf5-fbfb9a966da3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg87

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

lemma sg2046_oai : RowSquare [4,3,1,1,1,1,1,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg179

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2046_oai := @OAI.UniversalTensorSquare.sg2046_oai
