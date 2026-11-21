-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39872
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:59.196137+00:00
-- url     : https://prove2.me/submissions/f270295f-d9d5-45ed-9b18-c0a2bf3e2ed4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16334
import Theorems.Thm_OAI_UniversalTensorSquare_sg20716

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 98. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39872_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,8,8,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16334

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39872_oai := @OAI.UniversalTensorSquare.sg39872_oai
