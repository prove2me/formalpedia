-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42296
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:12:39.134905+00:00
-- url     : https://prove2.me/submissions/0016a0be-c2dc-432d-8791-b3f819fa10b2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg19133
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 104. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42296_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19133

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42296_oai := @OAI.UniversalTensorSquare.sg42296_oai
