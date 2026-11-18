-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg372
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:20:21.05562+00:00
-- url     : https://prove2.me/submissions/5292ea17-14b2-4082-bc6f-b444166c589d

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

lemma sgCert372 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 = 20 := by
  decide +kernel

lemma sg372_oai : RowSquare [5,1,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB372 sgT372 sgFlag372
  change solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 ≠ 0
  rw [sgCert372]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg372_oai := @OAI.UniversalTensorSquare.sg372_oai
