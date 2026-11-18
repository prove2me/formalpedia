-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35458
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T11:11:47.177972+00:00
-- url     : https://prove2.me/submissions/177a0d12-0777-4dd9-aac3-724f60c79c55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20758
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg4378

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

lemma sgCert828 : solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB828 sgT828) sgFlag828 = 5 := by
  decide +kernel

lemma sg828 : RowSquare [4,2,2,1,1] [2,2,2,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,1,1]) (ts := [6,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB828 sgT828 sgFlag828
  change solveCompact 10 (.full [6,4]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [6,4] (Equiv.refl (Fin 10)) sgB828 sgT828) sgFlag828 ≠ 0
  rw [sgCert828]
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

lemma sg3410 : RowSquare [7,3,3,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg828

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

lemma sg16264 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg3410 sg4378

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 87. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35458_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,11,7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20758 sg16264

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35458_oai := @OAI.UniversalTensorSquare.sg35458_oai
