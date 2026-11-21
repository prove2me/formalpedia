-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_43All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:20:50.142851+00:00
-- url     : https://prove2.me/submissions/a3d1ea80-11eb-4d99-88d1-c90592f327ed

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_42All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10221
import Theorems.Thm_OAI_UniversalTensorSquare_sg10230
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg24192
import Theorems.Thm_OAI_UniversalTensorSquare_sg24194
import Theorems.Thm_OAI_UniversalTensorSquare_sg24196
import Theorems.Thm_OAI_UniversalTensorSquare_sg24197
import Theorems.Thm_OAI_UniversalTensorSquare_sg24199
import Theorems.Thm_OAI_UniversalTensorSquare_sg24200
import Theorems.Thm_OAI_UniversalTensorSquare_sg24201
import Theorems.Thm_OAI_UniversalTensorSquare_sg24202
import Theorems.Thm_OAI_UniversalTensorSquare_sg24203
import Theorems.Thm_OAI_UniversalTensorSquare_sg24204
import Theorems.Thm_OAI_UniversalTensorSquare_sg24206
import Theorems.Thm_OAI_UniversalTensorSquare_sg24207
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg8438
import Theorems.Thm_OAI_UniversalTensorSquare_sg8441
import Theorems.Thm_OAI_UniversalTensorSquare_sg909
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert143

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

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
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

lemma sg1647 : RowSquare [4,3,2,1,1,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg143

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

lemma sg10115 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1647

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

lemma sg24193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10115

lemma sg24195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10195

lemma sg24198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10230

lemma sg24205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8441 sg10195

lemma sg24208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10221

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_41All : degreeTree43_41.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24200,⟨sg24196,⟨sg24194,⟨sg24193,⟨sg24192,True.intro,True.intro⟩,True.intro⟩,⟨sg24195,True.intro,True.intro⟩⟩,⟨sg24198,⟨sg24197,True.intro,True.intro⟩,⟨sg24199,True.intro,True.intro⟩⟩⟩,⟨sg24204,⟨sg24202,⟨sg24201,True.intro,True.intro⟩,⟨sg24203,True.intro,True.intro⟩⟩,⟨sg24206,⟨sg24205,True.intro,True.intro⟩,⟨sg24207,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_43All_oai : degreeTree43_43.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24208,degreeTree43_41All,degreeTree43_42All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_43All_oai := @OAI.UniversalTensorSquare.degreeTree43_43All_oai
