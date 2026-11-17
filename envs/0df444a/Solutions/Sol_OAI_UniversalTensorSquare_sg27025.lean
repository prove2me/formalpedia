-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg27025
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:58:25.989209+00:00
-- url     : https://prove2.me/submissions/e1689a54-cb45-4486-9884-33a1a426a69b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21214

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

lemma sgCert575 : solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB575 sgT575) sgFlag575 = 2 := by
  decide +kernel

lemma sg575 : RowSquare [4,3,1,1] [4,4,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [3,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB575 sgT575 sgFlag575
  change solveCompact 9 (.full [3,2,2,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [3,2,2,2] (Equiv.refl (Fin 9)) sgB575 sgT575) sgFlag575 ≠ 0
  rw [sgCert575]
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

lemma sg27025_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg575 sg21214

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg27025_oai := @OAI.UniversalTensorSquare.sg27025_oai
