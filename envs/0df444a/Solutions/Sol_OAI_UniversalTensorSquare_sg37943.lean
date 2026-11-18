-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg37943
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T15:17:40.544423+00:00
-- url     : https://prove2.me/submissions/92d0e95a-4af6-4d1a-a9a2-e960cd93a835

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20682

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6504 : RowSquare [10,3,2,2,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16649 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1682 sg6504

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37943_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,7,7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20682

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg37943_oai := @OAI.UniversalTensorSquare.sg37943_oai
