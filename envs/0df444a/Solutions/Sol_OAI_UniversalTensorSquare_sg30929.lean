-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg30929
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T03:15:11.177407+00:00
-- url     : https://prove2.me/submissions/c298837a-9547-4133-bc71-466975e1a036

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1337
import Theorems.Thm_OAI_UniversalTensorSquare_sg1358
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415

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

lemma sg10493 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,2,2] := by
  exact rowSquare_join (by decide) sg1337 sg1358

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 75. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30929_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10493

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg30929_oai := @OAI.UniversalTensorSquare.sg30929_oai
