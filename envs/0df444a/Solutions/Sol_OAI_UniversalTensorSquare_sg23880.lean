-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23880
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T03:51:52.099281+00:00
-- url     : https://prove2.me/submissions/63a9241a-70b5-42b5-9d44-7d92e319d83f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg8730

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

lemma sgCert961 : solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 = 4 := by
  decide +kernel

lemma sg961 : RowSquare [5,3,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB961 sgT961 sgFlag961
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 ≠ 0
  rw [sgCert961]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1421 : RowSquare [6,3,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg961

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

lemma sg9448 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1421

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23880_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9448

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23880_oai := @OAI.UniversalTensorSquare.sg23880_oai
