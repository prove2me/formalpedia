-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6914
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:14:11.304428+00:00
-- url     : https://prove2.me/submissions/8a6e2d26-b5f3-4570-bd84-51ab05fa70c7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6914_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg999

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6914_oai := @OAI.UniversalTensorSquare.sg6914_oai
