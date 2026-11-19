-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg876
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:28:32.461515+00:00
-- url     : https://prove2.me/submissions/5e0bbb7e-9975-4648-a160-d4b301649a33

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert876

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

lemma sg876_oai : RowSquare [4,3,3] [3,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [8,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB876 sgT876 sgFlag876
  change solveCompact 10 (.full [8,1,1]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,1,1] (Equiv.refl (Fin 10)) sgB876 sgT876) sgFlag876 ≠ 0
  rw [sgCert876]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg876_oai := @OAI.UniversalTensorSquare.sg876_oai
