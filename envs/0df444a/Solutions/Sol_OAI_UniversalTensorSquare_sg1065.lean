-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1065
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:35:37.354199+00:00
-- url     : https://prove2.me/submissions/8ecac97b-3bd5-45f9-8af8-7723d9d1765b

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert1065

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

lemma sg1065_oai : RowSquare [6,2,2] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1065 sgT1065 sgFlag1065
  change solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB1065 sgT1065) sgFlag1065 ≠ 0
  rw [sgCert1065]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1065_oai := @OAI.UniversalTensorSquare.sg1065_oai
