-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32009
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T01:44:59.545542+00:00
-- url     : https://prove2.me/submissions/ede7c864-5393-4378-9635-68066f96a36a

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg31942
import Theorems.Thm_OAI_UniversalTensorSquare_sg459

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

lemma sgCert496 : solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB496 sgT496) sgFlag496 = -1 := by
  decide +kernel

lemma sg496 : RowSquare [3,3,1,1,1] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB496 sgT496 sgFlag496
  change solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB496 sgT496) sgFlag496 ≠ 0
  rw [sgCert496]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5696 : RowSquare [6,5,2,2,2,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg496 sg459

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32009_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5696 sg31942

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32009_oai := @OAI.UniversalTensorSquare.sg32009_oai
