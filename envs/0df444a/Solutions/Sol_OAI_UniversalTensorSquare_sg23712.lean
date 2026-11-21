-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23712
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:14:15.386505+00:00
-- url     : https://prove2.me/submissions/5b0f7fe0-982a-47e4-95b6-1e46f6859a40

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1875 : RowSquare [7,2,1,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8222 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1875

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

lemma sg9687 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8222

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23712_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8648 sg9687

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23712_oai := @OAI.UniversalTensorSquare.sg23712_oai
