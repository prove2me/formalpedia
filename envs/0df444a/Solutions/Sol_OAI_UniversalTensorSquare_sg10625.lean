-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10625
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:50:45.66858+00:00
-- url     : https://prove2.me/submissions/99103700-bdd6-42b0-b2ca-cc1ce6e15a73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2260
import Theorems.Thm_OAI_UniversalTensorSquare_sg588

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10625_oai : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2260

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10625_oai := @OAI.UniversalTensorSquare.sg10625_oai
