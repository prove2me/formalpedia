-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg17317
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:41:44.28638+00:00
-- url     : https://prove2.me/submissions/a5897f14-3d72-4b01-bd82-287af1c859bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg13739

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17317_oai : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg13739

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg17317_oai := @OAI.UniversalTensorSquare.sg17317_oai
