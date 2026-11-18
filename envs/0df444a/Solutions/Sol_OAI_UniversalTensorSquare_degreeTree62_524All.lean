-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_524All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:21:11.110293+00:00
-- url     : https://prove2.me/submissions/aa834055-b3ec-42c1-8acc-467b70e66cd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_520All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_521All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_522All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg37751
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg577
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg6501 : RowSquare [9,5,3,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg577 sg912

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

lemma sg14902 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg998 sg6501

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

lemma sg17409 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14902

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37773 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,6,6,6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17409

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

lemma degreeTree62_523All : degreeTree62_523.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37773,degreeTree62_521All,degreeTree62_522All⟩

lemma degreeTree62_524All_oai : degreeTree62_524.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37751,degreeTree62_520All,degreeTree62_523All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_524All_oai := @OAI.UniversalTensorSquare.degreeTree62_524All_oai
