-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37079
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T06:46:42.078366+00:00
-- url     : https://prove2.me/submissions/a2bf9d4f-f61f-4f58-a51d-4bd58036a0cd

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18913
import Theorems.Thm_OAI_UniversalTensorSquare_sg19867
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 91. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37079_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,5,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19867

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37079_oai := @OAI.UniversalTensorSquare.sg37079_oai
