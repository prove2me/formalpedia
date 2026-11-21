-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39546
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T14:23:08.533452+00:00
-- url     : https://prove2.me/submissions/d3471fd0-27cd-44f8-a6be-d86808dfeabf

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11748
import Theorems.Thm_OAI_UniversalTensorSquare_sg165
import Theorems.Thm_OAI_UniversalTensorSquare_sg185
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg74

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

lemma sgCert484 : solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB484 sgT484) sgFlag484 = 1 := by
  decide +kernel

lemma sg484 : RowSquare [3,2,2,2] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,2,2,2]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB484 sgT484 sgFlag484
  change solveCompact 9 (.full [3,3,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [3,3,3] (Equiv.refl (Fin 9)) sgB484 sgT484) sgFlag484 ≠ 0
  rw [sgCert484]
  norm_num

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

lemma sg3614 : RowSquare [8,3,2,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4263 : RowSquare [7,3,3,3] [6,6,4] := by
  exact rowSquare_join (by decide) sg185 sg484

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15958 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4263

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

lemma sg20851 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 97. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39546_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,9,5,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15958

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39546_oai := @OAI.UniversalTensorSquare.sg39546_oai
