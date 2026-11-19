-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4467
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:25:56.833491+00:00
-- url     : https://prove2.me/submissions/8ae833c5-31c9-4a41-b8f6-731e830542fc

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg890
import Theorems.Thm_OAI_UniversalTensorSquare_sg97

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4467_oai : RowSquare [9,3,1,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg890

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4467_oai := @OAI.UniversalTensorSquare.sg4467_oai
