-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_12All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:45:44.697123+00:00
-- url     : https://prove2.me/submissions/e594e64d-19f4-4148-96c9-04ac9ccc6f5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10099
import Theorems.Thm_OAI_UniversalTensorSquare_sg23822
import Theorems.Thm_OAI_UniversalTensorSquare_sg23823
import Theorems.Thm_OAI_UniversalTensorSquare_sg23824
import Theorems.Thm_OAI_UniversalTensorSquare_sg23825
import Theorems.Thm_OAI_UniversalTensorSquare_sg23826
import Theorems.Thm_OAI_UniversalTensorSquare_sg23827
import Theorems.Thm_OAI_UniversalTensorSquare_sg23828
import Theorems.Thm_OAI_UniversalTensorSquare_sg23829
import Theorems.Thm_OAI_UniversalTensorSquare_sg23830
import Theorems.Thm_OAI_UniversalTensorSquare_sg23832
import Theorems.Thm_OAI_UniversalTensorSquare_sg23833
import Theorems.Thm_OAI_UniversalTensorSquare_sg23834
import Theorems.Thm_OAI_UniversalTensorSquare_sg23835
import Theorems.Thm_OAI_UniversalTensorSquare_sg23836
import Theorems.Thm_OAI_UniversalTensorSquare_sg8525

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10099

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

lemma degreeTree43_12All_oai : degreeTree43_12.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23829,⟨sg23825,⟨sg23823,⟨sg23822,True.intro,True.intro⟩,⟨sg23824,True.intro,True.intro⟩⟩,⟨sg23827,⟨sg23826,True.intro,True.intro⟩,⟨sg23828,True.intro,True.intro⟩⟩⟩,⟨sg23833,⟨sg23831,⟨sg23830,True.intro,True.intro⟩,⟨sg23832,True.intro,True.intro⟩⟩,⟨sg23835,⟨sg23834,True.intro,True.intro⟩,⟨sg23836,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_12All_oai := @OAI.UniversalTensorSquare.degreeTree43_12All_oai
