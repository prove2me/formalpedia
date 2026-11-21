-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7218
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:29:14.035968+00:00
-- url     : https://prove2.me/submissions/b5105803-60a6-4afb-af1f-61aa51362584

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1039
import Theorems.Thm_OAI_UniversalTensorSquare_sg372

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5235 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg1039

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg7218_oai : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5235

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7218_oai := @OAI.UniversalTensorSquare.sg7218_oai
