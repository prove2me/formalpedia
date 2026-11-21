-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_37All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:46:43.89621+00:00
-- url     : https://prove2.me/submissions/553c7fac-e711-4182-9b70-ec1580096234

import Mathlib
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_31All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_36All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg22166
import Theorems.Thm_OAI_UniversalTensorSquare_sg22167
import Theorems.Thm_OAI_UniversalTensorSquare_sg22168
import Theorems.Thm_OAI_UniversalTensorSquare_sg22169
import Theorems.Thm_OAI_UniversalTensorSquare_sg22171
import Theorems.Thm_OAI_UniversalTensorSquare_sg22172
import Theorems.Thm_OAI_UniversalTensorSquare_sg22173
import Theorems.Thm_OAI_UniversalTensorSquare_sg22174
import Theorems.Thm_OAI_UniversalTensorSquare_sg22175
import Theorems.Thm_OAI_UniversalTensorSquare_sg22176
import Theorems.Thm_OAI_UniversalTensorSquare_sg22177
import Theorems.Thm_OAI_UniversalTensorSquare_sg22178
import Theorems.Thm_OAI_UniversalTensorSquare_sg22179
import Theorems.Thm_OAI_UniversalTensorSquare_sg22180
import Theorems.Thm_OAI_UniversalTensorSquare_sg22181
import Theorems.Thm_OAI_UniversalTensorSquare_sg22183
import Theorems.Thm_OAI_UniversalTensorSquare_sg22184
import Theorems.Thm_OAI_UniversalTensorSquare_sg22186
import Theorems.Thm_OAI_UniversalTensorSquare_sg22188
import Theorems.Thm_OAI_UniversalTensorSquare_sg22189
import Theorems.Thm_OAI_UniversalTensorSquare_sg22191
import Theorems.Thm_OAI_UniversalTensorSquare_sg22192
import Theorems.Thm_OAI_UniversalTensorSquare_sg22193
import Theorems.Thm_OAI_UniversalTensorSquare_sg22194
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg615
import Theorems.Thm_OAI_UniversalTensorSquare_sg7378
import Theorems.Thm_OAI_UniversalTensorSquare_sg7387
import Theorems.Thm_OAI_UniversalTensorSquare_sg7388
import Theorems.Thm_OAI_UniversalTensorSquare_sg7389
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert614

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

lemma sg614 : RowSquare [5,2,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB614 sgT614 sgFlag614
  change solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 ≠ 0
  rw [sgCert614]
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

lemma sg1004 : RowSquare [6,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg6104 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1005

lemma sg6106 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1004

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6297 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg838

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7380 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6104

lemma sg7386 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6106

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22165 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7378

lemma sg22170 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7380

lemma sg22182 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7386

lemma sg22185 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7387

lemma sg22187 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7388

lemma sg22190 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,7,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7389

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_32All : degreeTree39_32.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22180,⟨sg22173,⟨sg22169,⟨sg22167,⟨sg22166,True.intro,True.intro⟩,⟨sg22168,True.intro,True.intro⟩⟩,⟨sg22171,⟨sg22170,True.intro,True.intro⟩,⟨sg22172,True.intro,True.intro⟩⟩⟩,⟨sg22177,⟨sg22175,⟨sg22174,True.intro,True.intro⟩,⟨sg22176,True.intro,True.intro⟩⟩,⟨sg22179,⟨sg22178,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22187,⟨sg22184,⟨sg22182,⟨sg22181,True.intro,True.intro⟩,⟨sg22183,True.intro,True.intro⟩⟩,⟨sg22186,⟨sg22185,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22191,⟨sg22189,⟨sg22188,True.intro,True.intro⟩,⟨sg22190,True.intro,True.intro⟩⟩,⟨sg22193,⟨sg22192,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_33All : degreeTree39_33.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22165,degreeTree39_31All,degreeTree39_32All⟩

lemma degreeTree39_37All_oai : degreeTree39_37.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22194,degreeTree39_33All,degreeTree39_36All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_37All_oai := @OAI.UniversalTensorSquare.degreeTree39_37All_oai
