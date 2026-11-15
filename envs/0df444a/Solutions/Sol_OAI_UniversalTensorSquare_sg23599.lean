-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23599
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T20:40:20.990335+00:00
-- url     : https://prove2.me/submissions/46452a01-ae61-4936-bd39-85e8344c472d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg14086

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

lemma sgCert877 : solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB877 sgT877) sgFlag877 = 72 := by
  decide +kernel

lemma sg877 : RowSquare [4,4,1,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB877 sgT877 sgFlag877
  change solveCompact 10 (.full [7,3]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [7,3] (Equiv.refl (Fin 10)) sgB877 sgT877) sgFlag877 ≠ 0
  rw [sgCert877]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2693 : RowSquare [6,6,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg877

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23599_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2693 sg14086

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23599_oai := @OAI.UniversalTensorSquare.sg23599_oai
