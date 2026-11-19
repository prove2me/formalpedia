-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7978
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:03:13.943277+00:00
-- url     : https://prove2.me/submissions/3b804ca8-b060-4593-88f5-c6aadc29c8c0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg749
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7978_oai : RowSquare [7,5,2,2,2,1,1] [8,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg749

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7978_oai := @OAI.UniversalTensorSquare.sg7978_oai
