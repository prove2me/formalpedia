-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25878
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:59:25.332924+00:00
-- url     : https://prove2.me/submissions/e4c325e0-d5a7-4b48-a029-21dd9961de17

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8726
import Theorems.Thm_OAI_UniversalTensorSquare_sg9492

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25878_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9492

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25878_oai := @OAI.UniversalTensorSquare.sg25878_oai
