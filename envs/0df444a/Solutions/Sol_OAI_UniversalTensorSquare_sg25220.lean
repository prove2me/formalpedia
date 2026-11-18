-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg25220
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:45:40.525375+00:00
-- url     : https://prove2.me/submissions/6d2bcba6-3971-4040-917c-da0659661fe0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg8666

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

lemma sg9682 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1758

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25220_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9682

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg25220_oai := @OAI.UniversalTensorSquare.sg25220_oai
