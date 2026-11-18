-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2051
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:49:18.25011+00:00
-- url     : https://prove2.me/submissions/d08c815d-2c78-4a03-bb2f-ceb0fba096b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg181
import Theorems.Thm_OAI_UniversalTensorSquare_sg87

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2051_oai : RowSquare [4,3,1,1,1,1,1,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg87 sg181

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2051_oai := @OAI.UniversalTensorSquare.sg2051_oai
