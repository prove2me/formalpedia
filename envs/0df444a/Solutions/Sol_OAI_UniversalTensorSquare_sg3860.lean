-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3860
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T13:17:45.545627+00:00
-- url     : https://prove2.me/submissions/03050759-f58d-42cb-98da-546fa8e2a168

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg561
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3860_oai : RowSquare [4,3,2,2,2,2,1] [4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg561

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3860_oai := @OAI.UniversalTensorSquare.sg3860_oai
