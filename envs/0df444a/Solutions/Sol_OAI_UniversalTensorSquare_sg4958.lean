-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4958
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:34:11.03344+00:00
-- url     : https://prove2.me/submissions/d2d8df85-9666-4da1-b1a9-edb4c2431053

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg194
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

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

lemma sg4958_oai : RowSquare [9,3,2,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg194 sg892

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4958_oai := @OAI.UniversalTensorSquare.sg4958_oai
