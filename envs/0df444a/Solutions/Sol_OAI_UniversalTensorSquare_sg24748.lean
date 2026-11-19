-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24748
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:34:44.99892+00:00
-- url     : https://prove2.me/submissions/9b116f8c-56f8-443d-84e8-0a513e9f58e7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10090
import Theorems.Thm_OAI_UniversalTensorSquare_sg8550

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24748_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg8550 sg10090

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24748_oai := @OAI.UniversalTensorSquare.sg24748_oai
