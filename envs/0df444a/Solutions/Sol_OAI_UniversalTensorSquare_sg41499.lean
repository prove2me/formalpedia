-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41499
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:06:50.558413+00:00
-- url     : https://prove2.me/submissions/fe7d0003-ad53-4940-aeb7-6b996e9c508a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15756
import Theorems.Thm_OAI_UniversalTensorSquare_sg20887

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 102. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41499_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,9,9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20887 sg15756

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41499_oai := @OAI.UniversalTensorSquare.sg41499_oai
