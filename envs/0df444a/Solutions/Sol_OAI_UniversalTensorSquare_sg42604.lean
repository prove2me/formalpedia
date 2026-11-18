-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42604
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:35:12.026325+00:00
-- url     : https://prove2.me/submissions/9b15b98c-df6e-488a-82b7-ebda19a62f60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg20152

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42604_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,12,7,7,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20152

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42604_oai := @OAI.UniversalTensorSquare.sg42604_oai
