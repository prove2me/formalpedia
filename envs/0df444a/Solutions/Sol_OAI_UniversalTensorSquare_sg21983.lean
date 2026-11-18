-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21983
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:57:34.280057+00:00
-- url     : https://prove2.me/submissions/92a20d55-6dbc-4e9d-88e3-cb40bb79254b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg915
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert143

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg6371 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg1755

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7044 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg915

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21983_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7044

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21983_oai := @OAI.UniversalTensorSquare.sg21983_oai
