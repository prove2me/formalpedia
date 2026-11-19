-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4504
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:26:29.356955+00:00
-- url     : https://prove2.me/submissions/c2295e1b-62a8-4acb-9e6b-18c74c469ea2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg179
import Theorems.Thm_OAI_UniversalTensorSquare_sg636

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

lemma sg4504_oai : RowSquare [9,3,3,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg636

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4504_oai := @OAI.UniversalTensorSquare.sg4504_oai
