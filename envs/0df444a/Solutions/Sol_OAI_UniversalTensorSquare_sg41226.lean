-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg41226
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:42:41.003495+00:00
-- url     : https://prove2.me/submissions/43213b25-cdc8-4d63-9d28-c68818945c69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15865
import Theorems.Thm_OAI_UniversalTensorSquare_sg20859

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 101. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41226_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,6,6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15865

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg41226_oai := @OAI.UniversalTensorSquare.sg41226_oai
