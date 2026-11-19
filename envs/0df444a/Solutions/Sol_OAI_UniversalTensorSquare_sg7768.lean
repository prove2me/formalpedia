-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7768
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:50:44.473303+00:00
-- url     : https://prove2.me/submissions/f533aeb8-7436-44fa-a460-67d5b2df9315

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg5412

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7768_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5412

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7768_oai := @OAI.UniversalTensorSquare.sg7768_oai
