-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10386
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:19:20.591553+00:00
-- url     : https://prove2.me/submissions/ac66fd78-e76c-4d19-9d5b-5da2c3e7dce8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1328
import Theorems.Thm_OAI_UniversalTensorSquare_sg1358

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10386_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1358

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10386_oai := @OAI.UniversalTensorSquare.sg10386_oai
