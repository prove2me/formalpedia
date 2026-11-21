-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27001
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:50:28.433557+00:00
-- url     : https://prove2.me/submissions/7966e897-337e-4165-9de6-34e213e9bd9e

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21134
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert958

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

lemma sg958 : RowSquare [5,3,1,1] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB958 sgT958 sgFlag958
  change solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB958 sgT958) sgFlag958 ≠ 0
  rw [sgCert958]
  norm_num

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

lemma sg27001_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg21134

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27001_oai := @OAI.UniversalTensorSquare.sg27001_oai
