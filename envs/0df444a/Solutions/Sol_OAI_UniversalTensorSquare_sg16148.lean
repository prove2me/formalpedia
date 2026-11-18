-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg16148
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:04:38.391795+00:00
-- url     : https://prove2.me/submissions/45f70020-42b2-4463-9d75-33ff21940044
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg3620
import Theorems.Thm_OAI_UniversalTensorSquare_sg4215

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

lemma sg16148_oai : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3620 sg4215

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg16148_oai := @OAI.UniversalTensorSquare.sg16148_oai
