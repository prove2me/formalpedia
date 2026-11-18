-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35466
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:59:12.029759+00:00
-- url     : https://prove2.me/submissions/81224517-f98d-493d-8654-9df32ee8823e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg16159
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert1001

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

lemma sgCert297 : solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 = -5 := by
  decide +kernel

lemma sg297 : RowSquare [3,3,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB297 sgT297 sgFlag297
  change solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 ≠ 0
  rw [sgCert297]
  norm_num

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

lemma sg20829 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg297 sg11429

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

lemma sg35466_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,11,9,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20829 sg16159

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35466_oai := @OAI.UniversalTensorSquare.sg35466_oai
