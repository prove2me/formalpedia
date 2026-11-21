-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14328
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:49.943123+00:00
-- url     : https://prove2.me/submissions/7937f8eb-822b-4eea-870b-80315696cd0e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2372
import Theorems.Thm_OAI_UniversalTensorSquare_sg2724

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14328_oai : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2372 sg2724

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14328_oai := @OAI.UniversalTensorSquare.sg14328_oai
