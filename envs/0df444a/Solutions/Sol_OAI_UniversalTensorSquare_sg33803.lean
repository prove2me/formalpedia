-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33803
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T07:40:28.30519+00:00
-- url     : https://prove2.me/submissions/5cc7e977-9c81-42b8-bd99-58ebbdae54f6

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2137
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251

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

lemma sgCert295 : solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 = 10 := by
  decide +kernel

lemma sg295 : RowSquare [3,3,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB295 sgT295 sgFlag295
  change solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 ≠ 0
  rw [sgCert295]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert373 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 = 24 := by
  decide +kernel

lemma sg373 : RowSquare [5,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB373 sgT373 sgFlag373
  change solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 ≠ 0
  rw [sgCert373]
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

lemma sgCert922 : solveCompact 10 (.full [4,4,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB922 sgT922) sgFlag922 = 4 := by
  decide +kernel

lemma sg922 : RowSquare [5,2,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [5,2,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB922 sgT922 sgFlag922
  change solveCompact 10 (.full [4,4,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB922 sgT922) sgFlag922 ≠ 0
  rw [sgCert922]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert1000 : solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
    (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 = 72 := by
  decide +kernel

lemma sg1000 : RowSquare [6,1,1,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [6,1,1,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1000 sgT1000 sgFlag1000
  change solveCompact 10 (.full [6,4]) (.full [6,1,1,1,1]) (.full [6,1,1,1,1])
    (certificateEdges [6,1,1,1,1] [6,1,1,1,1] [6,4] (Equiv.refl (Fin 10)) sgB1000 sgT1000) sgFlag1000 ≠ 0
  rw [sgCert1000]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5786 : RowSquare [10,3,2,2,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg922

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

lemma sg11428 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16140 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2137 sg5786

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20821 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11428

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

lemma sg33803_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20821 sg16140

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33803_oai := @OAI.UniversalTensorSquare.sg33803_oai
