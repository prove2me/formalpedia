-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41258
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:50:48.122896+00:00
-- url     : https://prove2.me/submissions/9b53d954-54b1-451b-af22-e7ece0e07770

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15867
import Theorems.Thm_OAI_UniversalTensorSquare_sg20859

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 101. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41258_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,7,5,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15867

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41258_oai := @OAI.UniversalTensorSquare.sg41258_oai
