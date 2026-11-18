-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35622
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T05:09:40.289527+00:00
-- url     : https://prove2.me/submissions/9478b72d-053f-45cb-bccb-fb952d1d9a4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg18914
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg2708
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
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

lemma sg1758 : RowSquare [6,2,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg265

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

lemma sg3595 : RowSquare [8,3,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1758

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

lemma sg15175 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3595

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

lemma sg19777 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15175

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 87. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35622_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,7,7,7,7,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19777

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35622_oai := @OAI.UniversalTensorSquare.sg35622_oai
