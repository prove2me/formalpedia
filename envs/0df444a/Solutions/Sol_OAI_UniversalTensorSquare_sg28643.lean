-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28643
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T15:07:19.286841+00:00
-- url     : https://prove2.me/submissions/eef54bd5-f0b7-442b-922a-f2dd0828e680

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21237

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

lemma sgCert570 : solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB570 sgT570) sgFlag570 = -1 := by
  decide +kernel

lemma sg570 : RowSquare [4,3,1,1] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB570 sgT570 sgFlag570
  change solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB570 sgT570) sgFlag570 ≠ 0
  rw [sgCert570]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28643_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg570 sg21237

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28643_oai := @OAI.UniversalTensorSquare.sg28643_oai
