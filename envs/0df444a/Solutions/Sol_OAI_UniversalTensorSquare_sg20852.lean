-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20852
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:14:53.007048+00:00
-- url     : https://prove2.me/submissions/eaa1d79d-3a7f-47b3-af34-b21d9c862a61

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11748
import Theorems.Thm_OAI_UniversalTensorSquare_sg166

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20852_oai : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11748

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20852_oai := @OAI.UniversalTensorSquare.sg20852_oai
