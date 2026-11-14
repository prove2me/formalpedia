-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg15672
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:30:31.509719+00:00
-- url     : https://prove2.me/submissions/70388ac5-70a0-4edb-82f2-99ce2633fc74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg4842

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15672_oai : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4842

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg15672_oai := @OAI.UniversalTensorSquare.sg15672_oai
