-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25884
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:57:29.318307+00:00
-- url     : https://prove2.me/submissions/6c40c9e5-22f1-429e-aaba-dcfdf9b558b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10272
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430

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

lemma sg25884_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10272

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25884_oai := @OAI.UniversalTensorSquare.sg25884_oai
