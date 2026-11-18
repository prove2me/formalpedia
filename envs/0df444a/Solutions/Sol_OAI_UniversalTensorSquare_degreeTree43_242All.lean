-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_242All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:30.333799+00:00
-- url     : https://prove2.me/submissions/5a78286c-9bdb-4211-a7eb-2fe6ce254b33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_222All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_223All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_224All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_226All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_230All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_236All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_237All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_238All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10298
import Theorems.Thm_OAI_UniversalTensorSquare_sg10306
import Theorems.Thm_OAI_UniversalTensorSquare_sg1039
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg26644
import Theorems.Thm_OAI_UniversalTensorSquare_sg26709
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg8730
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1260 : RowSquare [5,2,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg809

lemma sg1437 : RowSquare [6,3,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg68

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1779 : RowSquare [6,3,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg313

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7781 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9218 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1779

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8762 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg892 sg1260

lemma sg8802 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7781

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9451 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1039 sg1754

lemma sg9508 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1437

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10306

lemma sg26532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9218

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10298

lemma sg26580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9508

lemma sg26741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8762 sg9451

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

lemma degreeTree43_225All : degreeTree43_225.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26532,degreeTree43_223All,degreeTree43_224All⟩

lemma degreeTree43_227All : degreeTree43_227.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26548,degreeTree43_225All,degreeTree43_226All⟩

lemma degreeTree43_231All : degreeTree43_231.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26580,degreeTree43_227All,degreeTree43_230All⟩

lemma degreeTree43_239All : degreeTree43_239.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26741,degreeTree43_237All,degreeTree43_238All⟩

lemma degreeTree43_240All : degreeTree43_240.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26709,degreeTree43_236All,degreeTree43_239All⟩

lemma degreeTree43_241All : degreeTree43_241.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26644,degreeTree43_231All,degreeTree43_240All⟩

lemma degreeTree43_242All_oai : degreeTree43_242.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26515,degreeTree43_222All,degreeTree43_241All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_242All_oai := @OAI.UniversalTensorSquare.degreeTree43_242All_oai
