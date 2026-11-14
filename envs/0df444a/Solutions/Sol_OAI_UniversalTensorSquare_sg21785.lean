-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21785
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T02:31:34.164936+00:00
-- url     : https://prove2.me/submissions/2e0bc557-4f08-4134-aad5-6d9f5703c30d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6418
import Theorems.Thm_OAI_UniversalTensorSquare_sg6775

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21785_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6775

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21785_oai := @OAI.UniversalTensorSquare.sg21785_oai
