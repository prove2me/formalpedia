-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg20525
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:40:10.926086+00:00
-- url     : https://prove2.me/submissions/793d8ef3-601c-4de9-bc50-15069782d2e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2708
import Theorems.Thm_OAI_UniversalTensorSquare_sg4834

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20525_oai : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4834

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg20525_oai := @OAI.UniversalTensorSquare.sg20525_oai
