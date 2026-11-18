-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20906
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:29:23.156841+00:00
-- url     : https://prove2.me/submissions/1b3eb5d8-9b9b-4d1a-b76e-caccb12e1e7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg4319
import Theorems.Thm_OAI_UniversalTensorSquare_sg4358

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20906_oai : RowSquare [6,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4319 sg4358

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20906_oai := @OAI.UniversalTensorSquare.sg20906_oai
