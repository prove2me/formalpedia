-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2551
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:57:28.66922+00:00
-- url     : https://prove2.me/submissions/b77ba997-f172-444d-83e2-56c7767d4030

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg180

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2551_oai : RowSquare [4,4,1,1,1,1,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg180

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2551_oai := @OAI.UniversalTensorSquare.sg2551_oai
