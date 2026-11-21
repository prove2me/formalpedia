-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_397All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:31:29.964626+00:00
-- url     : https://prove2.me/submissions/40533cf5-35d9-4aae-8819-525f2772e9ff

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1499
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg36393
import Theorems.Thm_OAI_UniversalTensorSquare_sg36394
import Theorems.Thm_OAI_UniversalTensorSquare_sg36395
import Theorems.Thm_OAI_UniversalTensorSquare_sg36396
import Theorems.Thm_OAI_UniversalTensorSquare_sg36397
import Theorems.Thm_OAI_UniversalTensorSquare_sg36398
import Theorems.Thm_OAI_UniversalTensorSquare_sg36399
import Theorems.Thm_OAI_UniversalTensorSquare_sg36400
import Theorems.Thm_OAI_UniversalTensorSquare_sg36401
import Theorems.Thm_OAI_UniversalTensorSquare_sg36402
import Theorems.Thm_OAI_UniversalTensorSquare_sg36403
import Theorems.Thm_OAI_UniversalTensorSquare_sg36404
import Theorems.Thm_OAI_UniversalTensorSquare_sg36405
import Theorems.Thm_OAI_UniversalTensorSquare_sg36406
import Theorems.Thm_OAI_UniversalTensorSquare_sg36408
import Theorems.Thm_OAI_UniversalTensorSquare_sg36409
import Theorems.Thm_OAI_UniversalTensorSquare_sg36410
import Theorems.Thm_OAI_UniversalTensorSquare_sg36411
import Theorems.Thm_OAI_UniversalTensorSquare_sg36412
import Theorems.Thm_OAI_UniversalTensorSquare_sg36413
import Theorems.Thm_OAI_UniversalTensorSquare_sg46

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

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

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

lemma sg5754 : RowSquare [8,5,3,1,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg912

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14875 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1499 sg5754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17364 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14875

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36407 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,6,6,6,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17364

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_397All_oai : degreeTree62_397.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36403,⟨sg36398,⟨sg36395,⟨sg36394,⟨sg36393,True.intro,True.intro⟩,True.intro⟩,⟨sg36397,⟨sg36396,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36401,⟨sg36400,⟨sg36399,True.intro,True.intro⟩,True.intro⟩,⟨sg36402,True.intro,True.intro⟩⟩⟩,⟨sg36409,⟨sg36406,⟨sg36405,⟨sg36404,True.intro,True.intro⟩,True.intro⟩,⟨sg36408,⟨sg36407,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36412,⟨sg36411,⟨sg36410,True.intro,True.intro⟩,True.intro⟩,⟨sg36413,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_397All_oai := @OAI.UniversalTensorSquare.degreeTree62_397All_oai
