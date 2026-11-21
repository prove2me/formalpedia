-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42084
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:56:13.237201+00:00
-- url     : https://prove2.me/submissions/656c09e8-9e1f-4add-9c79-723868eafe4c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17754
import Theorems.Thm_OAI_UniversalTensorSquare_sg20518

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42084_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17754

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42084_oai := @OAI.UniversalTensorSquare.sg42084_oai
