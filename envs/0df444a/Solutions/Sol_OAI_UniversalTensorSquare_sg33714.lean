-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33714
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T07:36:44.220214+00:00
-- url     : https://prove2.me/submissions/e8359399-dfca-4d14-a750-60c94aa5da4a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17290
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 82. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33714_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,8,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17290

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33714_oai := @OAI.UniversalTensorSquare.sg33714_oai
