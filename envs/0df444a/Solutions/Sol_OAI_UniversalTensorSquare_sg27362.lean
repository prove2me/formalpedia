-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27362
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T12:20:40.151164+00:00
-- url     : https://prove2.me/submissions/e2bd74e1-3dc1-44b4-ba70-3d7336c5c2d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8660
import Theorems.Thm_OAI_UniversalTensorSquare_sg9732

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 67. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27362_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9732

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27362_oai := @OAI.UniversalTensorSquare.sg27362_oai
