-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34756
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:31:49.511208+00:00
-- url     : https://prove2.me/submissions/d4f6e142-f5cc-45e3-a69f-4728105073ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1262
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg74
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert163 : solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 = -3 := by
  decide +kernel

lemma sg163 : RowSquare [3,2,2] [4,3] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB163 sgT163 sgFlag163
  change solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 ≠ 0
  rw [sgCert163]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1874 : RowSquare [7,2,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4963 : RowSquare [9,3,2,1,1,1] [5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg89 sg1262

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3324 : RowSquare [6,3,3,1,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg265

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11733 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg1874

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15668 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11733

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20956 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4963

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 85. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34756_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,6,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg15668 sg20956

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34756_oai := @OAI.UniversalTensorSquare.sg34756_oai
