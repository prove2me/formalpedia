-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4988
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:36:54.910832+00:00
-- url     : https://prove2.me/submissions/dc315d58-983d-48b3-920f-be8f1091e805

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg535

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4988_oai : RowSquare [9,4,2,1,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg535

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4988_oai := @OAI.UniversalTensorSquare.sg4988_oai
