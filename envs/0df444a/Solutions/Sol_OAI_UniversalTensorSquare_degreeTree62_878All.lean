-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_878All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:26:25.224717+00:00
-- url     : https://prove2.me/submissions/2f7a0657-17c3-4a4c-b46d-f3dcd857f097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg41700
import Theorems.Thm_OAI_UniversalTensorSquare_sg41702
import Theorems.Thm_OAI_UniversalTensorSquare_sg41703
import Theorems.Thm_OAI_UniversalTensorSquare_sg41704
import Theorems.Thm_OAI_UniversalTensorSquare_sg41705
import Theorems.Thm_OAI_UniversalTensorSquare_sg41706
import Theorems.Thm_OAI_UniversalTensorSquare_sg41707
import Theorems.Thm_OAI_UniversalTensorSquare_sg41708
import Theorems.Thm_OAI_UniversalTensorSquare_sg41709
import Theorems.Thm_OAI_UniversalTensorSquare_sg41710
import Theorems.Thm_OAI_UniversalTensorSquare_sg41711
import Theorems.Thm_OAI_UniversalTensorSquare_sg41712
import Theorems.Thm_OAI_UniversalTensorSquare_sg41713
import Theorems.Thm_OAI_UniversalTensorSquare_sg41714
import Theorems.Thm_OAI_UniversalTensorSquare_sg41715
import Theorems.Thm_OAI_UniversalTensorSquare_sg41716
import Theorems.Thm_OAI_UniversalTensorSquare_sg41717
import Theorems.Thm_OAI_UniversalTensorSquare_sg41718
import Theorems.Thm_OAI_UniversalTensorSquare_sg41720
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg940

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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1061 : RowSquare [6,2,2] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

lemma sg1069 : RowSquare [6,3,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

lemma sg1107 : RowSquare [7,2,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg88

lemma sg1117 : RowSquare [7,3] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg46

lemma sg1202 : RowSquare [4,3,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg940

lemma sg1203 : RowSquare [4,3,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

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

lemma sg6537 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1061 sg1117

lemma sg6540 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1069 sg1107

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18816 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg6540

lemma sg18818 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg6537

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 102. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41701 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,5,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18816

lemma sg41719 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,6,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18818

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

lemma degreeTree62_878All_oai : degreeTree62_878.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41710,⟨sg41705,⟨sg41702,⟨sg41701,⟨sg41700,True.intro,True.intro⟩,True.intro⟩,⟨sg41704,⟨sg41703,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41708,⟨sg41707,⟨sg41706,True.intro,True.intro⟩,True.intro⟩,⟨sg41709,True.intro,True.intro⟩⟩⟩,⟨sg41716,⟨sg41713,⟨sg41712,⟨sg41711,True.intro,True.intro⟩,True.intro⟩,⟨sg41715,⟨sg41714,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41719,⟨sg41718,⟨sg41717,True.intro,True.intro⟩,True.intro⟩,⟨sg41720,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_878All_oai := @OAI.UniversalTensorSquare.degreeTree62_878All_oai
