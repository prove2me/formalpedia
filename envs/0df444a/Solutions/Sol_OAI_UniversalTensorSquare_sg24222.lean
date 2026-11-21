-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:34:31.657459+00:00
-- url     : https://prove2.me/submissions/362574dd-5427-4277-b4fb-ff62bf19ddbc

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg459

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg821 : RowSquare [4,2,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg459

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8758 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg1327

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg9441 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1416

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24222_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8758 sg9441

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24222_oai := @OAI.UniversalTensorSquare.sg24222_oai
