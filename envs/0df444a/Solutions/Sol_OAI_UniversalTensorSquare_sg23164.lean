-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23164
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T09:01:12.619237+00:00
-- url     : https://prove2.me/submissions/f96a77b3-1838-4076-b20e-4b533d32f223

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6369
import Theorems.Thm_OAI_UniversalTensorSquare_sg7155

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23164_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7155

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23164_oai := @OAI.UniversalTensorSquare.sg23164_oai
