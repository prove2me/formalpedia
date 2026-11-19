-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23689
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:03:10.80867+00:00
-- url     : https://prove2.me/submissions/56dbe57a-b0ed-429b-8d87-6854040ca0bf

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11736
import Theorems.Thm_OAI_UniversalTensorSquare_sg6398

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23689_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6398 sg11736

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23689_oai := @OAI.UniversalTensorSquare.sg23689_oai
