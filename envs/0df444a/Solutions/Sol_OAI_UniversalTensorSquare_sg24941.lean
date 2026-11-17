-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24941
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T06:42:52.962786+00:00
-- url     : https://prove2.me/submissions/fb6e60be-88dd-45eb-9759-4288557eea34

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg15004

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

lemma sgCert885 : solveCompact 10 (.full [5,3,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,3,2] (Equiv.refl (Fin 10)) sgB885 sgT885) sgFlag885 = -1 := by
  decide +kernel

lemma sg885 : RowSquare [4,4,1,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB885 sgT885 sgFlag885
  change solveCompact 10 (.full [5,3,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,3,2] (Equiv.refl (Fin 10)) sgB885 sgT885) sgFlag885 ≠ 0
  rw [sgCert885]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2695 : RowSquare [6,6,1,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg885

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24941_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2695 sg15004

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24941_oai := @OAI.UniversalTensorSquare.sg24941_oai
