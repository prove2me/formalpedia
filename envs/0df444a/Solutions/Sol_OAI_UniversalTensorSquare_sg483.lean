-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg483
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:30:16.223209+00:00
-- url     : https://prove2.me/submissions/16eb6b1d-5c2a-4127-b322-0796a55e16c9

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact

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

lemma sgCert483 : solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB483 sgT483) sgFlag483 = -2 := by
  decide +kernel

lemma sg483_oai : RowSquare [3,2,2,2] [3,3,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [5,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB483 sgT483 sgFlag483
  change solveCompact 9 (.full [5,2,2]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,2,2] (Equiv.refl (Fin 9)) sgB483 sgT483) sgFlag483 ≠ 0
  rw [sgCert483]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg483_oai := @OAI.UniversalTensorSquare.sg483_oai
