-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg11903
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T20:51:42.106832+00:00
-- url     : https://prove2.me/submissions/58e606a9-9375-46ab-8774-deb25901c274
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg34

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

lemma sgCert768 : solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB768 sgT768) sgFlag768 = -16 := by
  decide +kernel

lemma sg768 : RowSquare [3,3,1,1,1,1] [3,3,3,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB768 sgT768 sgFlag768
  change solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB768 sgT768) sgFlag768 ≠ 0
  rw [sgCert768]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

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

lemma sg1163 : RowSquare [3,3,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg34 sg91

lemma sg1213 : RowSquare [4,3,1,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg768

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10901 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1163

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

lemma sg11521 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10901

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11903_oai : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11521

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg11903_oai := @OAI.UniversalTensorSquare.sg11903_oai
