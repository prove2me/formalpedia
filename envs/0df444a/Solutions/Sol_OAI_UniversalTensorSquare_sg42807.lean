-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg42807
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T19:35:54.053535+00:00
-- url     : https://prove2.me/submissions/22196adf-4460-4382-94e7-10065c22984f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg489
import Theorems.Thm_OAI_UniversalTensorSquare_sg587

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1503 : RowSquare [7,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg587

lemma sg1552 : RowSquare [8,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8958 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1503 sg1552

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20189 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8958

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42807_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,7,7,6,6,6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20189

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg42807_oai := @OAI.UniversalTensorSquare.sg42807_oai
