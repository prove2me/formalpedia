-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23308
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T13:25:02.891818+00:00
-- url     : https://prove2.me/submissions/b9b18eb1-1f4f-46bc-a507-ad1d69f11ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg7753

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23308_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7753

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23308_oai := @OAI.UniversalTensorSquare.sg23308_oai
