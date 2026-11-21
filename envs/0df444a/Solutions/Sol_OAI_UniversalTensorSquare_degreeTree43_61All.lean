-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_61All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:30.232766+00:00
-- url     : https://prove2.me/submissions/9bebcbe7-92b1-4252-8044-1aee5c173087

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10228
import Theorems.Thm_OAI_UniversalTensorSquare_sg10229
import Theorems.Thm_OAI_UniversalTensorSquare_sg10230
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg24467
import Theorems.Thm_OAI_UniversalTensorSquare_sg24469
import Theorems.Thm_OAI_UniversalTensorSquare_sg24470
import Theorems.Thm_OAI_UniversalTensorSquare_sg24471
import Theorems.Thm_OAI_UniversalTensorSquare_sg24476
import Theorems.Thm_OAI_UniversalTensorSquare_sg24479
import Theorems.Thm_OAI_UniversalTensorSquare_sg24480
import Theorems.Thm_OAI_UniversalTensorSquare_sg24481
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg8559
import Theorems.Thm_OAI_UniversalTensorSquare_sg9493
import Theorems.Thm_OAI_UniversalTensorSquare_sg9727

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10640 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg8559

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9727

lemma sg24472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9493

lemma sg24473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10230

lemma sg24474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10640

lemma sg24475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10228

lemma sg24477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10229

lemma sg24478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10229

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

lemma degreeTree43_61All_oai : degreeTree43_61.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24474,⟨sg24470,⟨sg24468,⟨sg24467,True.intro,True.intro⟩,⟨sg24469,True.intro,True.intro⟩⟩,⟨sg24472,⟨sg24471,True.intro,True.intro⟩,⟨sg24473,True.intro,True.intro⟩⟩⟩,⟨sg24478,⟨sg24476,⟨sg24475,True.intro,True.intro⟩,⟨sg24477,True.intro,True.intro⟩⟩,⟨sg24480,⟨sg24479,True.intro,True.intro⟩,⟨sg24481,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_61All_oai := @OAI.UniversalTensorSquare.degreeTree43_61All_oai
