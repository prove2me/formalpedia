-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7096
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:22:14.050202+00:00
-- url     : https://prove2.me/submissions/113b09f8-bfaf-41c6-bdd7-b44c94049429

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1378
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7096_oai : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1378

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7096_oai := @OAI.UniversalTensorSquare.sg7096_oai
