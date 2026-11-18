-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35393
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:04:12.124473+00:00
-- url     : https://prove2.me/submissions/a9ce7c42-784d-42e0-b4c3-1f2a7a84d083
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg334
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sgCert310 : solveCompact 8 (.full [4,4]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [4,4] (Equiv.refl (Fin 8)) sgB310 sgT310) sgFlag310 = -2 := by
  decide +kernel

lemma sg310 : RowSquare [3,3,2] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,2]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB310 sgT310 sgFlag310
  change solveCompact 8 (.full [4,4]) (.full [3,3,2]) (.full [3,3,2])
    (certificateEdges [3,3,2] [3,3,2] [4,4] (Equiv.refl (Fin 8)) sgB310 sgT310) sgFlag310 ≠ 0
  rw [sgCert310]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4922 : RowSquare [8,4,3,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg310 sg586

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

lemma sg4508 : RowSquare [9,4,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg334

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12918 : RowSquare [5,5,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg4922

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14705 : RowSquare [6,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4508

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15639 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg12918

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21041 : RowSquare [8,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14705

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

lemma sg35393_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,11,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg15639 sg21041

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35393_oai := @OAI.UniversalTensorSquare.sg35393_oai
