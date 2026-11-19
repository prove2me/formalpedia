-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13324
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:04:22.911438+00:00
-- url     : https://prove2.me/submissions/e6d4cf36-f22c-407b-9a9e-ba7beb3de422

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1637
import Theorems.Thm_OAI_UniversalTensorSquare_sg2555

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13324_oai : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1637 sg2555

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13324_oai := @OAI.UniversalTensorSquare.sg13324_oai
