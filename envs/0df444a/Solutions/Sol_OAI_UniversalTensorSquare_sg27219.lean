-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27219
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T12:08:59.824011+00:00
-- url     : https://prove2.me/submissions/860aaadc-c53e-49ed-b925-64e13661bab1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12686

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert371 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 = 24 := by
  decide +kernel

lemma sg371 : RowSquare [5,1,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB371 sgT371 sgFlag371
  change solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 ≠ 0
  rw [sgCert371]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert964 : solveCompact 10 (.full [6,2,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB964 sgT964) sgFlag964 = 6 := by
  decide +kernel

lemma sg964 : RowSquare [5,3,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB964 sgT964 sgFlag964
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB964 sgT964) sgFlag964 ≠ 0
  rw [sgCert964]
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

lemma sg5263 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg964

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27219_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5263 sg12686

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27219_oai := @OAI.UniversalTensorSquare.sg27219_oai
