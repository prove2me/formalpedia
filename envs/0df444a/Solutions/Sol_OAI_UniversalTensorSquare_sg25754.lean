-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25754
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:56:44.389434+00:00
-- url     : https://prove2.me/submissions/8e9c83ac-9554-4f7c-a1c0-6ea4064eb05c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10299
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25754_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10299

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25754_oai := @OAI.UniversalTensorSquare.sg25754_oai
