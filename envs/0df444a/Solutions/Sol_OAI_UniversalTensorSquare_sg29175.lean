-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29175
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T16:09:19.766319+00:00
-- url     : https://prove2.me/submissions/7910c51a-9126-4f6f-a6bc-738b9cd97365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21239

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

lemma sgCert569 : solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB569 sgT569) sgFlag569 = 10 := by
  decide +kernel

lemma sg569 : RowSquare [4,3,1,1] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB569 sgT569 sgFlag569
  change solveCompact 9 (.full [5,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,2,2] (Equiv.refl (Fin 9)) sgB569 sgT569) sgFlag569 ≠ 0
  rw [sgCert569]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29175_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg569 sg21239

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29175_oai := @OAI.UniversalTensorSquare.sg29175_oai
