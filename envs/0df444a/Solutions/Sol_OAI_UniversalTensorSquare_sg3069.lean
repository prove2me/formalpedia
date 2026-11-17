-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3069
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T22:46:29.246648+00:00
-- url     : https://prove2.me/submissions/8940b2de-21f4-42e3-9a73-1e306a5e6d2f

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

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

lemma sgCert637 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB637 sgT637) sgFlag637 = 24 := by
  decide +kernel

lemma sg637 : RowSquare [5,2,2] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB637 sgT637 sgFlag637
  change solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB637 sgT637) sgFlag637 ≠ 0
  rw [sgCert637]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3069_oai : RowSquare [8,3,3] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg637

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3069_oai := @OAI.UniversalTensorSquare.sg3069_oai
