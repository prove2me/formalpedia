-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34241
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:39:15.620123+00:00
-- url     : https://prove2.me/submissions/7311823e-f9e1-42ff-ab55-e17add1b2a7b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16150
import Theorems.Thm_OAI_UniversalTensorSquare_sg20819

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34241_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20819 sg16150

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34241_oai := @OAI.UniversalTensorSquare.sg34241_oai
