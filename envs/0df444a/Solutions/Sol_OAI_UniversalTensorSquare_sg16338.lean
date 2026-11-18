-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg16338
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:14:55.938051+00:00
-- url     : https://prove2.me/submissions/7a849b54-a793-4606-973d-35c00228106a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg14576
import Theorems.Thm_OAI_UniversalTensorSquare_sg4

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16338_oai : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14576

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg16338_oai := @OAI.UniversalTensorSquare.sg16338_oai
