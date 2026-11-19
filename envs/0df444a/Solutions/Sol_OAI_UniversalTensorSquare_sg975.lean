-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg975
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:07:10.392387+00:00
-- url     : https://prove2.me/submissions/73ef3d65-a718-4977-a085-8048871c2b6d

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert975

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

lemma sg975_oai : RowSquare [5,3,2] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB975 sgT975 sgFlag975
  change solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB975 sgT975) sgFlag975 ≠ 0
  rw [sgCert975]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg975_oai := @OAI.UniversalTensorSquare.sg975_oai
