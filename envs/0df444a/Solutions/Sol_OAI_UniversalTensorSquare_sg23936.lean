-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23936
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:15:20.450574+00:00
-- url     : https://prove2.me/submissions/7e32dc58-e58c-4fb3-a032-131dd6d3ad4f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert915 : solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 = -6 := by
  decide +kernel

lemma sg915 : RowSquare [5,2,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB915 sgT915 sgFlag915
  change solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 ≠ 0
  rw [sgCert915]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2288 : RowSquare [7,3,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg586

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

lemma sg6292 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg915

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

lemma sg8835 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6292

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9158 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg2288

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

lemma sg23936_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8835 sg9158

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23936_oai := @OAI.UniversalTensorSquare.sg23936_oai
