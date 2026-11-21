-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21700
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:23:48.069335+00:00
-- url     : https://prove2.me/submissions/9778ec49-8deb-4ba4-893a-2d5cb6ac1ace

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6151
import Theorems.Thm_OAI_UniversalTensorSquare_sg7558

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21700_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7558

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21700_oai := @OAI.UniversalTensorSquare.sg21700_oai
