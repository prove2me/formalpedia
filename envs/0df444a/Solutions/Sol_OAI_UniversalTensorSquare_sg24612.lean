-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24612
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:30:56.799375+00:00
-- url     : https://prove2.me/submissions/96449e29-6687-4fbf-beb6-c60108ea5d11

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg1423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9502 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1423

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24612_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9502

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24612_oai := @OAI.UniversalTensorSquare.sg24612_oai
