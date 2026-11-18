-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_3All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:59:48.856533+00:00
-- url     : https://prove2.me/submissions/06833021-600e-4b4d-ac31-0c4620fd2d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21730
import Theorems.Thm_OAI_UniversalTensorSquare_sg21731
import Theorems.Thm_OAI_UniversalTensorSquare_sg21732
import Theorems.Thm_OAI_UniversalTensorSquare_sg21733
import Theorems.Thm_OAI_UniversalTensorSquare_sg21734
import Theorems.Thm_OAI_UniversalTensorSquare_sg21735
import Theorems.Thm_OAI_UniversalTensorSquare_sg21736
import Theorems.Thm_OAI_UniversalTensorSquare_sg21737
import Theorems.Thm_OAI_UniversalTensorSquare_sg21738
import Theorems.Thm_OAI_UniversalTensorSquare_sg21739
import Theorems.Thm_OAI_UniversalTensorSquare_sg21740
import Theorems.Thm_OAI_UniversalTensorSquare_sg21741
import Theorems.Thm_OAI_UniversalTensorSquare_sg21742
import Theorems.Thm_OAI_UniversalTensorSquare_sg21743
import Theorems.Thm_OAI_UniversalTensorSquare_sg21744
import Theorems.Thm_OAI_UniversalTensorSquare_sg21745
import Theorems.Thm_OAI_UniversalTensorSquare_sg21746
import Theorems.Thm_OAI_UniversalTensorSquare_sg21747
import Theorems.Thm_OAI_UniversalTensorSquare_sg21748
import Theorems.Thm_OAI_UniversalTensorSquare_sg21749
import Theorems.Thm_OAI_UniversalTensorSquare_sg21751
import Theorems.Thm_OAI_UniversalTensorSquare_sg21752
import Theorems.Thm_OAI_UniversalTensorSquare_sg21753
import Theorems.Thm_OAI_UniversalTensorSquare_sg21754
import Theorems.Thm_OAI_UniversalTensorSquare_sg21756
import Theorems.Thm_OAI_UniversalTensorSquare_sg21757
import Theorems.Thm_OAI_UniversalTensorSquare_sg6409
import Theorems.Thm_OAI_UniversalTensorSquare_sg6410

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

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

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

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

lemma sg5892 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1417

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

lemma sg6794 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5892

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21750 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6794

lemma sg21755 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6794

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

lemma degreeTree39_3All_oai : degreeTree39_3.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21744,⟨sg21737,⟨sg21733,⟨sg21731,⟨sg21730,True.intro,True.intro⟩,⟨sg21732,True.intro,True.intro⟩⟩,⟨sg21735,⟨sg21734,True.intro,True.intro⟩,⟨sg21736,True.intro,True.intro⟩⟩⟩,⟨sg21741,⟨sg21739,⟨sg21738,True.intro,True.intro⟩,⟨sg21740,True.intro,True.intro⟩⟩,⟨sg21743,⟨sg21742,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21751,⟨sg21748,⟨sg21746,⟨sg21745,True.intro,True.intro⟩,⟨sg21747,True.intro,True.intro⟩⟩,⟨sg21750,⟨sg21749,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21755,⟨sg21753,⟨sg21752,True.intro,True.intro⟩,⟨sg21754,True.intro,True.intro⟩⟩,⟨sg21757,⟨sg21756,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_3All_oai := @OAI.UniversalTensorSquare.degreeTree39_3All_oai
