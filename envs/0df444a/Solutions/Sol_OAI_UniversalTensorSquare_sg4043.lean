-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4043
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T15:30:52.804052+00:00
-- url     : https://prove2.me/submissions/713af45e-1ae2-4c57-8726-7f31c18b5812

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg759

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

lemma sg4043_oai : RowSquare [6,3,3,3,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg68 sg759

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4043_oai := @OAI.UniversalTensorSquare.sg4043_oai
