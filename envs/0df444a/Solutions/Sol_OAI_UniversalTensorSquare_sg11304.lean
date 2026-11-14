-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11304
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:15:28.994402+00:00
-- url     : https://prove2.me/submissions/ef1e4001-d181-43ee-a4c9-649b7c708883
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1335
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11304_oai : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1756

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11304_oai := @OAI.UniversalTensorSquare.sg11304_oai
