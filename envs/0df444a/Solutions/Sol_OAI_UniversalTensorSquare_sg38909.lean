-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38909
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:01:20.293238+00:00
-- url     : https://prove2.me/submissions/8b58d595-9a1c-488b-953f-cf5df7c23363

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15756
import Theorems.Thm_OAI_UniversalTensorSquare_sg20864

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38909_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15756

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38909_oai := @OAI.UniversalTensorSquare.sg38909_oai
