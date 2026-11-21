-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_150All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:10:51.67011+00:00
-- url     : https://prove2.me/submissions/7e1975cc-f795-4c09-8890-faf8afb2d528

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10098
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg25612
import Theorems.Thm_OAI_UniversalTensorSquare_sg25613
import Theorems.Thm_OAI_UniversalTensorSquare_sg25614
import Theorems.Thm_OAI_UniversalTensorSquare_sg25615
import Theorems.Thm_OAI_UniversalTensorSquare_sg25616
import Theorems.Thm_OAI_UniversalTensorSquare_sg25617
import Theorems.Thm_OAI_UniversalTensorSquare_sg25618
import Theorems.Thm_OAI_UniversalTensorSquare_sg25619
import Theorems.Thm_OAI_UniversalTensorSquare_sg25620
import Theorems.Thm_OAI_UniversalTensorSquare_sg25621
import Theorems.Thm_OAI_UniversalTensorSquare_sg25622
import Theorems.Thm_OAI_UniversalTensorSquare_sg25623
import Theorems.Thm_OAI_UniversalTensorSquare_sg25624
import Theorems.Thm_OAI_UniversalTensorSquare_sg25625
import Theorems.Thm_OAI_UniversalTensorSquare_sg25626

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

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

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

lemma sg1009 : RowSquare [6,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg312

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

lemma sg8560 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1009 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8560 sg10098

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

lemma degreeTree43_150All_oai : degreeTree43_150.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25620,⟨sg25616,⟨sg25614,⟨sg25613,⟨sg25612,True.intro,True.intro⟩,True.intro⟩,⟨sg25615,True.intro,True.intro⟩⟩,⟨sg25618,⟨sg25617,True.intro,True.intro⟩,⟨sg25619,True.intro,True.intro⟩⟩⟩,⟨sg25624,⟨sg25622,⟨sg25621,True.intro,True.intro⟩,⟨sg25623,True.intro,True.intro⟩⟩,⟨sg25626,⟨sg25625,True.intro,True.intro⟩,⟨sg25627,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_150All_oai := @OAI.UniversalTensorSquare.degreeTree43_150All_oai
