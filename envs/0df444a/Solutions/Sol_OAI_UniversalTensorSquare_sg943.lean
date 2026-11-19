-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg943
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:52:05.516219+00:00
-- url     : https://prove2.me/submissions/1cfc0091-32a8-45d9-a005-8d039768ef2b

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert943

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

lemma sg943_oai : RowSquare [5,2,2,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB943 sgT943 sgFlag943
  change solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB943 sgT943) sgFlag943 ≠ 0
  rw [sgCert943]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg943_oai := @OAI.UniversalTensorSquare.sg943_oai
