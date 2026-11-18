-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4083
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:12:40.176499+00:00
-- url     : https://prove2.me/submissions/84a72997-ae71-4249-b662-ea6b913b6c53

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1631

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

lemma sg4083_oai : RowSquare [6,4,2,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg1631

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4083_oai := @OAI.UniversalTensorSquare.sg4083_oai
