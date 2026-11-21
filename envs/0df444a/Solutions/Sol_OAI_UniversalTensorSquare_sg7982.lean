-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7982
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:03:32.173594+00:00
-- url     : https://prove2.me/submissions/b4fb27ce-526e-4e8c-83cc-8d3341fe37eb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg115
import Theorems.Thm_OAI_UniversalTensorSquare_sg2132
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

lemma sg7982_oai : RowSquare [7,5,2,2,2,1,1] [8,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg2132

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7982_oai := @OAI.UniversalTensorSquare.sg7982_oai
