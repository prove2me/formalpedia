-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35590
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:47:51.61067+00:00
-- url     : https://prove2.me/submissions/372d60e4-d94b-4244-89ef-7cee754c44c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17215
import Theorems.Thm_OAI_UniversalTensorSquare_sg20529

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 87. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35590_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,7,7,7,6,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17215

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35590_oai := @OAI.UniversalTensorSquare.sg35590_oai
