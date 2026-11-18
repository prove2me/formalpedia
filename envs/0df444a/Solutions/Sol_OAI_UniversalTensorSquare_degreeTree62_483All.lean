-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_483All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:25:55.647785+00:00
-- url     : https://prove2.me/submissions/074d3675-690c-4e25-a8cf-4763a7f582e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11213
import Theorems.Thm_OAI_UniversalTensorSquare_sg18482
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg37358
import Theorems.Thm_OAI_UniversalTensorSquare_sg37359
import Theorems.Thm_OAI_UniversalTensorSquare_sg37360
import Theorems.Thm_OAI_UniversalTensorSquare_sg37361
import Theorems.Thm_OAI_UniversalTensorSquare_sg37363
import Theorems.Thm_OAI_UniversalTensorSquare_sg37364
import Theorems.Thm_OAI_UniversalTensorSquare_sg37366
import Theorems.Thm_OAI_UniversalTensorSquare_sg37367
import Theorems.Thm_OAI_UniversalTensorSquare_sg37368
import Theorems.Thm_OAI_UniversalTensorSquare_sg37369
import Theorems.Thm_OAI_UniversalTensorSquare_sg37370
import Theorems.Thm_OAI_UniversalTensorSquare_sg37371
import Theorems.Thm_OAI_UniversalTensorSquare_sg37372
import Theorems.Thm_OAI_UniversalTensorSquare_sg37373
import Theorems.Thm_OAI_UniversalTensorSquare_sg37374
import Theorems.Thm_OAI_UniversalTensorSquare_sg37375
import Theorems.Thm_OAI_UniversalTensorSquare_sg37377
import Theorems.Thm_OAI_UniversalTensorSquare_sg37378

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19886 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11213

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 92. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37362 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,8,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19886

lemma sg37365 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,8,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19886

lemma sg37376 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,8,6,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18482

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

lemma degreeTree62_483All_oai : degreeTree62_483.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37368,⟨sg37363,⟨sg37360,⟨sg37359,⟨sg37358,True.intro,True.intro⟩,True.intro⟩,⟨sg37362,⟨sg37361,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37366,⟨sg37365,⟨sg37364,True.intro,True.intro⟩,True.intro⟩,⟨sg37367,True.intro,True.intro⟩⟩⟩,⟨sg37374,⟨sg37371,⟨sg37370,⟨sg37369,True.intro,True.intro⟩,True.intro⟩,⟨sg37373,⟨sg37372,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37377,⟨sg37376,⟨sg37375,True.intro,True.intro⟩,True.intro⟩,⟨sg37378,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_483All_oai := @OAI.UniversalTensorSquare.degreeTree62_483All_oai
