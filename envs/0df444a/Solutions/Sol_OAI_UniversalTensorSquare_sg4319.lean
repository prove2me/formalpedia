-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4319
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:21:05.341474+00:00
-- url     : https://prove2.me/submissions/54f2e01b-99be-4f90-a4d5-afdf6d82cbfb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg315

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4319_oai : RowSquare [7,4,3,1,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg315

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4319_oai := @OAI.UniversalTensorSquare.sg4319_oai
