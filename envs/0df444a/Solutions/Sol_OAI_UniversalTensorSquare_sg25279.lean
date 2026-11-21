-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25279
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T07:12:10.683191+00:00
-- url     : https://prove2.me/submissions/3a305485-ac7b-4377-8877-d6623fd006ce

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8867
import Theorems.Thm_OAI_UniversalTensorSquare_sg9000

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25279_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8867 sg9000

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25279_oai := @OAI.UniversalTensorSquare.sg25279_oai
