-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10375
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:14:53.37388+00:00
-- url     : https://prove2.me/submissions/9a84a97e-a9de-46ee-b8b4-ff0fe1e938f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg6949

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

lemma sg10375_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6949

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10375_oai := @OAI.UniversalTensorSquare.sg10375_oai
