-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg834
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:15:57.463198+00:00
-- url     : https://prove2.me/submissions/610f6e18-03c3-41e3-989c-4e97e75b4b06

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert834

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

lemma sg834_oai : RowSquare [4,2,2,2] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB834 sgT834 sgFlag834
  change solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 ≠ 0
  rw [sgCert834]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg834_oai := @OAI.UniversalTensorSquare.sg834_oai
