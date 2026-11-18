-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33900
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:30:43.985629+00:00
-- url     : https://prove2.me/submissions/378bef36-74c5-4d02-b517-493f25a05ba0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18042
import Theorems.Thm_OAI_UniversalTensorSquare_sg20498

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33900_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18042

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33900_oai := @OAI.UniversalTensorSquare.sg33900_oai
