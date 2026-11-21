-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_164All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:42:47.542204+00:00
-- url     : https://prove2.me/submissions/d9210158-b407-45e0-ba48-7936748fe760

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10268
import Theorems.Thm_OAI_UniversalTensorSquare_sg10300
import Theorems.Thm_OAI_UniversalTensorSquare_sg10377
import Theorems.Thm_OAI_UniversalTensorSquare_sg25759
import Theorems.Thm_OAI_UniversalTensorSquare_sg25760
import Theorems.Thm_OAI_UniversalTensorSquare_sg25761
import Theorems.Thm_OAI_UniversalTensorSquare_sg25762
import Theorems.Thm_OAI_UniversalTensorSquare_sg25763
import Theorems.Thm_OAI_UniversalTensorSquare_sg25764
import Theorems.Thm_OAI_UniversalTensorSquare_sg25766
import Theorems.Thm_OAI_UniversalTensorSquare_sg25767
import Theorems.Thm_OAI_UniversalTensorSquare_sg25768
import Theorems.Thm_OAI_UniversalTensorSquare_sg25770
import Theorems.Thm_OAI_UniversalTensorSquare_sg25771
import Theorems.Thm_OAI_UniversalTensorSquare_sg25772
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425

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

lemma sg25758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10300

lemma sg25765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10268

lemma sg25769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10377

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

lemma degreeTree43_164All_oai : degreeTree43_164.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25765,⟨sg25761,⟨sg25759,⟨sg25758,True.intro,True.intro⟩,⟨sg25760,True.intro,True.intro⟩⟩,⟨sg25763,⟨sg25762,True.intro,True.intro⟩,⟨sg25764,True.intro,True.intro⟩⟩⟩,⟨sg25769,⟨sg25767,⟨sg25766,True.intro,True.intro⟩,⟨sg25768,True.intro,True.intro⟩⟩,⟨sg25771,⟨sg25770,True.intro,True.intro⟩,⟨sg25772,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_164All_oai := @OAI.UniversalTensorSquare.degreeTree43_164All_oai
