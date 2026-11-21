-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10336
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:11:27.676198+00:00
-- url     : https://prove2.me/submissions/4a7b0ca9-5a2d-471a-968f-5ca7d67e42d7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6927

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10336_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6927

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10336_oai := @OAI.UniversalTensorSquare.sg10336_oai
