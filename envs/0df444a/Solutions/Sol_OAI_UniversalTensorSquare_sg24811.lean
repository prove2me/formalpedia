-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24811
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:15:10.384628+00:00
-- url     : https://prove2.me/submissions/3941e2a5-5ea1-4c2e-bac6-779c6f383f02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12688

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert614 : solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 = -4 := by
  decide +kernel

lemma sg614 : RowSquare [5,2,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB614 sgT614 sgFlag614
  change solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 ≠ 0
  rw [sgCert614]
  norm_num

lemma sgCert615 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 = 13 := by
  decide +kernel

lemma sg615 : RowSquare [5,2,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB615 sgT615 sgFlag615
  change solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 ≠ 0
  rw [sgCert615]
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

lemma sg5245 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg615

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24811_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5245 sg12688

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24811_oai := @OAI.UniversalTensorSquare.sg24811_oai
