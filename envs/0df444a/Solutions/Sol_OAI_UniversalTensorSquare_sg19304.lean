-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg19304
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:17:45.069595+00:00
-- url     : https://prove2.me/submissions/82e38ff3-0863-4bb5-bbaf-91b55b75f04e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg15128

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19304_oai : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15128

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg19304_oai := @OAI.UniversalTensorSquare.sg19304_oai
