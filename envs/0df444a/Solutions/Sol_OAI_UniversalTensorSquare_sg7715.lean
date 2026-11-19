-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7715
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:49:53.037304+00:00
-- url     : https://prove2.me/submissions/766020c4-d1c4-496c-a716-48ff788e7e4e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1006
import Theorems.Thm_OAI_UniversalTensorSquare_sg903
import Definitions.Def_OAIQ259US001
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7715_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1006 sg903

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7715_oai := @OAI.UniversalTensorSquare.sg7715_oai
