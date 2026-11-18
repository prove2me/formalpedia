-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32455
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T03:42:21.592206+00:00
-- url     : https://prove2.me/submissions/ef4ab331-8983-49c2-a6d8-e12ca9cb8b15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg792

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

lemma sgCert296 : solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 = 6 := by
  decide +kernel

lemma sg296 : RowSquare [3,3,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB296 sgT296 sgFlag296
  change solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 ≠ 0
  rw [sgCert296]
  norm_num

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4439 : RowSquare [9,2,2,2,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11429 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16131 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3359 sg4439

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20827 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg296 sg11429

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32455_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20827 sg16131

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32455_oai := @OAI.UniversalTensorSquare.sg32455_oai
