-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg28496
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:38:49.622415+00:00
-- url     : https://prove2.me/submissions/cd70c8e6-c8e9-4268-a258-b251aa571a17

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg21263

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

lemma sgCert553 : solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB553 sgT553) sgFlag553 = 5 := by
  decide +kernel

lemma sg553 : RowSquare [4,2,2,1] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB553 sgT553 sgFlag553
  change solveCompact 9 (.full [4,3,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [4,3,2] (Equiv.refl (Fin 9)) sgB553 sgT553) sgFlag553 ≠ 0
  rw [sgCert553]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28496_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg553 sg21263

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg28496_oai := @OAI.UniversalTensorSquare.sg28496_oai
