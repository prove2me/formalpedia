-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38763
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:44:23.448139+00:00
-- url     : https://prove2.me/submissions/10632a70-c99d-484c-848d-a58415651e8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg16286
import Theorems.Thm_OAI_UniversalTensorSquare_sg20716

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38763_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16286

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38763_oai := @OAI.UniversalTensorSquare.sg38763_oai
