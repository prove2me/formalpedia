-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23637
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:11:57.002198+00:00
-- url     : https://prove2.me/submissions/f305a59a-132b-469b-a617-1a8c90db9d7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg7526
import Theorems.Thm_OAI_UniversalTensorSquare_sg8400

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23637_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7526 sg8400

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23637_oai := @OAI.UniversalTensorSquare.sg23637_oai
