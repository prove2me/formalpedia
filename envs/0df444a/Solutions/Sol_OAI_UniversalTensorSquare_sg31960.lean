-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg31960
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T03:30:35.537195+00:00
-- url     : https://prove2.me/submissions/87cedb92-3bca-4774-87e8-cfaae1e5e8b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg792

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2902 : RowSquare [8,2,2,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg586

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

lemma sg9444 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3359 : RowSquare [6,4,3,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg792

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14978 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3359

lemma sg15278 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg9444

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31960_oai : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15278 sg14978

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg31960_oai := @OAI.UniversalTensorSquare.sg31960_oai
