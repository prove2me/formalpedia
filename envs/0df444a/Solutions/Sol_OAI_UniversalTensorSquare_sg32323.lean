-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32323
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T02:03:31.748207+00:00
-- url     : https://prove2.me/submissions/488eaa26-1615-4f82-abf3-41ca660bce8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20884

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

lemma sgCert792 : solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB792 sgT792) sgFlag792 = -14 := by
  decide +kernel

lemma sg792 : RowSquare [3,3,2,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,2,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB792 sgT792 sgFlag792
  change solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB792 sgT792) sgFlag792 ≠ 0
  rw [sgCert792]
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

lemma sg2925 : RowSquare [8,2,2,2] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4883 : RowSquare [7,4,3,2,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg792

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

lemma sg15699 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg4883

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32323_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20884 sg15699

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32323_oai := @OAI.UniversalTensorSquare.sg32323_oai
