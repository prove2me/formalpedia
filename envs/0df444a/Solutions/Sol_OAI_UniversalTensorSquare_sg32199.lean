-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32199
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T01:56:05.421734+00:00
-- url     : https://prove2.me/submissions/268f679c-5600-4ada-853d-1683839f7eb2

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17188
import Theorems.Thm_OAI_UniversalTensorSquare_sg20518

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32199_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17188

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32199_oai := @OAI.UniversalTensorSquare.sg32199_oai
