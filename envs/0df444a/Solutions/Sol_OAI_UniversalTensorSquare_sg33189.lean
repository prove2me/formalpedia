-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33189
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T04:53:52.511928+00:00
-- url     : https://prove2.me/submissions/e63c4769-2d2c-4959-85aa-d5ef3351a04c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16254
import Theorems.Thm_OAI_UniversalTensorSquare_sg20713

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33189_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16254

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33189_oai := @OAI.UniversalTensorSquare.sg33189_oai
