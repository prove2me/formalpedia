-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6398
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:00:57.460205+00:00
-- url     : https://prove2.me/submissions/e2a18724-43ed-49a5-b2d0-d532eb8ef974

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6398_oai : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg892

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6398_oai := @OAI.UniversalTensorSquare.sg6398_oai
