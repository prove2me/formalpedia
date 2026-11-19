-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg15677
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:08:36.617202+00:00
-- url     : https://prove2.me/submissions/7a4aefa2-630d-434b-8867-4390b601e3ce

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12925
import Theorems.Thm_OAI_UniversalTensorSquare_sg13

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15677_oai : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12925

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg15677_oai := @OAI.UniversalTensorSquare.sg15677_oai
