-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg873
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:28:08.914407+00:00
-- url     : https://prove2.me/submissions/173847e9-0f62-41b3-8f27-d198ff0b82b6

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert873

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

lemma sg873_oai : RowSquare [4,3,3] [2,2,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [8,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB873 sgT873 sgFlag873
  change solveCompact 10 (.full [8,2]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,2] (Equiv.refl (Fin 10)) sgB873 sgT873) sgFlag873 ≠ 0
  rw [sgCert873]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg873_oai := @OAI.UniversalTensorSquare.sg873_oai
