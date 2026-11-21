-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28572
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:45:01.661202+00:00
-- url     : https://prove2.me/submissions/d22442d6-0458-415c-86ec-9ae79dc83c97

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1860
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457

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

lemma sgCert982 : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 = 99 := by
  decide +kernel

lemma sg982 : RowSquare [5,4,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,2,2,2,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB982 sgT982 sgFlag982
  change solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 ≠ 0
  rw [sgCert982]
  norm_num

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

lemma sg1852 : RowSquare [6,5,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg982

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16196 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1852 sg6457

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28572_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,4,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1860 sg16196

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28572_oai := @OAI.UniversalTensorSquare.sg28572_oai
