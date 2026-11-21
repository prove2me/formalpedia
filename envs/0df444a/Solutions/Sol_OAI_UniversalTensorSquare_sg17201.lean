-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg17201
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:39:48.815186+00:00
-- url     : https://prove2.me/submissions/8065f497-04fa-4df4-95e3-2aab94d6fa16

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3554
import Theorems.Thm_OAI_UniversalTensorSquare_sg4304

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17201_oai : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3554 sg4304

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg17201_oai := @OAI.UniversalTensorSquare.sg17201_oai
