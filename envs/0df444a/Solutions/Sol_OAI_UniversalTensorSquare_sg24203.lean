-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24203
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T04:34:17.283585+00:00
-- url     : https://prove2.me/submissions/50d27d6e-d2cb-40c8-aee6-641f2ac71383

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682

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

lemma sgCert371 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 = 24 := by
  decide +kernel

lemma sg371 : RowSquare [5,1,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB371 sgT371 sgFlag371
  change solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB371 sgT371) sgFlag371 ≠ 0
  rw [sgCert371]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert909 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB909 sgT909) sgFlag909 = 6 := by
  decide +kernel

lemma sg909 : RowSquare [5,1,1,1,1,1] [5,5] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [2,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB909 sgT909 sgFlag909
  change solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB909 sgT909) sgFlag909 ≠ 0
  rw [sgCert909]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1332 : RowSquare [6,1,1,1,1,1] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg909

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6879 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1682

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

lemma sg8439 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6879

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10195 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1332 sg1332

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

lemma sg24203_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8439 sg10195

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24203_oai := @OAI.UniversalTensorSquare.sg24203_oai
