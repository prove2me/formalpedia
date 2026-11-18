-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39344
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:30:28.732673+00:00
-- url     : https://prove2.me/submissions/aad048f2-d55c-42f3-8372-7d754d328d7d

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg20852
import Theorems.Thm_OAI_UniversalTensorSquare_sg3635

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

lemma sgCert286 : solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 = -3 := by
  decide +kernel

lemma sg286 : RowSquare [3,2,2,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB286 sgT286 sgFlag286
  change solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 ≠ 0
  rw [sgCert286]
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

lemma sg3430 : RowSquare [7,3,3,2] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg286

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

lemma sg15357 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3430

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

lemma sg15905 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15357

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

lemma sg39344_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,7,7,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15905

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39344_oai := @OAI.UniversalTensorSquare.sg39344_oai
