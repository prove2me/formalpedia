-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7089
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:21:51.433973+00:00
-- url     : https://prove2.me/submissions/37d515de-176d-487a-829d-63535e7262d1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1377
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7089_oai : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1377

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7089_oai := @OAI.UniversalTensorSquare.sg7089_oai
