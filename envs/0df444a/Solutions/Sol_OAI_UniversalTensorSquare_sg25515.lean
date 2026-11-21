-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25515
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:57:31.525794+00:00
-- url     : https://prove2.me/submissions/113c0ee1-3440-41e7-8bf0-1c4c43b7fdd0

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10099
import Theorems.Thm_OAI_UniversalTensorSquare_sg8532

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25515_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10099

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25515_oai := @OAI.UniversalTensorSquare.sg25515_oai
