-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg26199
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T02:05:24.713593+00:00
-- url     : https://prove2.me/submissions/2db4bc2e-2fdd-4d58-ab5c-33ffbf139e31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg892
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9195

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7789 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg892

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

lemma sg8814 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7789

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26199_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8814 sg9195

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg26199_oai := @OAI.UniversalTensorSquare.sg26199_oai
