-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34635
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:25:49.142487+00:00
-- url     : https://prove2.me/submissions/8bf92e9e-d43e-48e8-8976-c208d6ec5a62

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1262
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg18914
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2736 : RowSquare [7,3,1,1,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1262

lemma sg2889 : RowSquare [8,2,1,1,1,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1330

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14738 : RowSquare [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2889 sg2736

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19751 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14738

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 85. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34635_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,5,5,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19751

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34635_oai := @OAI.UniversalTensorSquare.sg34635_oai
