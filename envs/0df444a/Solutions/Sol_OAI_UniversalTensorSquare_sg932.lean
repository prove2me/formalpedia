-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg932
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:47:59.803198+00:00
-- url     : https://prove2.me/submissions/b58507f3-e3e1-4883-80e1-762a460c2657

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert932

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

lemma sg932_oai : RowSquare [5,2,1,1,1] [4,4,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [3,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB932 sgT932 sgFlag932
  change solveCompact 10 (.full [3,3,2,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [3,3,2,2] (Equiv.refl (Fin 10)) sgB932 sgT932) sgFlag932 ≠ 0
  rw [sgCert932]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg932_oai := @OAI.UniversalTensorSquare.sg932_oai
