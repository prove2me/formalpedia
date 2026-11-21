-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_163All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:15.213616+00:00
-- url     : https://prove2.me/submissions/9df5be56-a70c-47e6-aa15-bae3d9e3be4d

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg25741
import Theorems.Thm_OAI_UniversalTensorSquare_sg25742
import Theorems.Thm_OAI_UniversalTensorSquare_sg25743
import Theorems.Thm_OAI_UniversalTensorSquare_sg25744
import Theorems.Thm_OAI_UniversalTensorSquare_sg25745
import Theorems.Thm_OAI_UniversalTensorSquare_sg25746
import Theorems.Thm_OAI_UniversalTensorSquare_sg25747
import Theorems.Thm_OAI_UniversalTensorSquare_sg25748
import Theorems.Thm_OAI_UniversalTensorSquare_sg25749
import Theorems.Thm_OAI_UniversalTensorSquare_sg25750
import Theorems.Thm_OAI_UniversalTensorSquare_sg25751
import Theorems.Thm_OAI_UniversalTensorSquare_sg25752
import Theorems.Thm_OAI_UniversalTensorSquare_sg25753
import Theorems.Thm_OAI_UniversalTensorSquare_sg25754
import Theorems.Thm_OAI_UniversalTensorSquare_sg25756
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9827

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9827

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

lemma degreeTree43_163All_oai : degreeTree43_163.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25749,⟨sg25745,⟨sg25743,⟨sg25742,⟨sg25741,True.intro,True.intro⟩,True.intro⟩,⟨sg25744,True.intro,True.intro⟩⟩,⟨sg25747,⟨sg25746,True.intro,True.intro⟩,⟨sg25748,True.intro,True.intro⟩⟩⟩,⟨sg25753,⟨sg25751,⟨sg25750,True.intro,True.intro⟩,⟨sg25752,True.intro,True.intro⟩⟩,⟨sg25755,⟨sg25754,True.intro,True.intro⟩,⟨sg25756,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_163All_oai := @OAI.UniversalTensorSquare.degreeTree43_163All_oai
