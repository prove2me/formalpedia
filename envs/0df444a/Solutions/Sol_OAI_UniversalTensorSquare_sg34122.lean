-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34122
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T08:07:27.664955+00:00
-- url     : https://prove2.me/submissions/4ee8be6f-f3cf-4176-aed6-f9b3cd86aeaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18928
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623

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

lemma sg34122_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg18928

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34122_oai := @OAI.UniversalTensorSquare.sg34122_oai
