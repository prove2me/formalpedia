-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37451
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:33:49.760866+00:00
-- url     : https://prove2.me/submissions/28634e8f-012b-41dd-b8a2-257f787029b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15748
import Theorems.Thm_OAI_UniversalTensorSquare_sg20859

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 92. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37451_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,8,7,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15748

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37451_oai := @OAI.UniversalTensorSquare.sg37451_oai
