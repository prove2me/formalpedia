-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39974
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:13:55.81821+00:00
-- url     : https://prove2.me/submissions/a89d014e-add8-47cb-9701-2bda94b1cfb4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16763
import Theorems.Thm_OAI_UniversalTensorSquare_sg20640

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39974_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,9,8,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16763

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39974_oai := @OAI.UniversalTensorSquare.sg39974_oai
