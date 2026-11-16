-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24315
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:42:33.206596+00:00
-- url     : https://prove2.me/submissions/bc1d641a-fa79-467d-861f-35b4c489bf90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sgCert390 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB390 sgT390) sgFlag390 = 7 := by
  decide +kernel

lemma sg390 : RowSquare [5,2,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB390 sgT390 sgFlag390
  change solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB390 sgT390) sgFlag390 ≠ 0
  rw [sgCert390]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert941 : solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB941 sgT941) sgFlag941 = 18 := by
  decide +kernel

lemma sg941 : RowSquare [5,2,2,1] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB941 sgT941 sgFlag941
  change solveCompact 10 (.full [7,3]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB941 sgT941) sgFlag941 ≠ 0
  rw [sgCert941]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

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

lemma sg5125 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg941

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10124 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5125

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24315_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10124

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24315_oai := @OAI.UniversalTensorSquare.sg24315_oai
