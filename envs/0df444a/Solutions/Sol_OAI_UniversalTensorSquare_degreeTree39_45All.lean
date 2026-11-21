-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_45All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:46:50.270087+00:00
-- url     : https://prove2.me/submissions/6778ed41-affc-41b7-801e-c21f0ec38f2b

import Mathlib
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_37All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_40All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_41All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_42All
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg22310
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6151
import Theorems.Thm_OAI_UniversalTensorSquare_sg7413
import Theorems.Thm_OAI_UniversalTensorSquare_sg7652
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
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

lemma sg22252 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7652

lemma sg22339 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6297 sg7413

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

lemma degreeTree39_43All : degreeTree39_43.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22339,degreeTree39_41All,degreeTree39_42All⟩

lemma degreeTree39_44All : degreeTree39_44.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22310,degreeTree39_40All,degreeTree39_43All⟩

lemma degreeTree39_45All_oai : degreeTree39_45.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22252,degreeTree39_37All,degreeTree39_44All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_45All_oai := @OAI.UniversalTensorSquare.degreeTree39_45All_oai
