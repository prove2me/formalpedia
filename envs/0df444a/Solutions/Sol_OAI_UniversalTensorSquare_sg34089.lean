-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34089
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T08:04:14.529672+00:00
-- url     : https://prove2.me/submissions/5fa37e93-3193-433b-b908-9b358e4d6202
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg2372

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

lemma sgCert899 : solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB899 sgT899) sgFlag899 = 36 := by
  decide +kernel

lemma sg899 : RowSquare [5,1,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB899 sgT899 sgFlag899
  change solveCompact 10 (.full [4,4,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB899 sgT899) sgFlag899 ≠ 0
  rw [sgCert899]
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

lemma sg2735 : RowSquare [7,3,1,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg899

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14365 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2372 sg2735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19745 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14365

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34089_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19745

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34089_oai := @OAI.UniversalTensorSquare.sg34089_oai
