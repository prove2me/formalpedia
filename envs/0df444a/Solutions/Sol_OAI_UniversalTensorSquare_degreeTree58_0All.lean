-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree58_0All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:29:25.988178+00:00
-- url     : https://prove2.me/submissions/7394ca59-dc06-4f11-b97b-cd6e2dd3f7e4

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15290
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg31951
import Theorems.Thm_OAI_UniversalTensorSquare_sg31952
import Theorems.Thm_OAI_UniversalTensorSquare_sg31953
import Theorems.Thm_OAI_UniversalTensorSquare_sg31954
import Theorems.Thm_OAI_UniversalTensorSquare_sg31955
import Theorems.Thm_OAI_UniversalTensorSquare_sg31956
import Theorems.Thm_OAI_UniversalTensorSquare_sg31957
import Theorems.Thm_OAI_UniversalTensorSquare_sg31958
import Theorems.Thm_OAI_UniversalTensorSquare_sg31959
import Theorems.Thm_OAI_UniversalTensorSquare_sg31960
import Theorems.Thm_OAI_UniversalTensorSquare_sg31962
import Theorems.Thm_OAI_UniversalTensorSquare_sg31963
import Theorems.Thm_OAI_UniversalTensorSquare_sg31964
import Theorems.Thm_OAI_UniversalTensorSquare_sg31965
import Theorems.Thm_OAI_UniversalTensorSquare_sg31966
import Theorems.Thm_OAI_UniversalTensorSquare_sg31967
import Theorems.Thm_OAI_UniversalTensorSquare_sg31968
import Theorems.Thm_OAI_UniversalTensorSquare_sg31969
import Theorems.Thm_OAI_UniversalTensorSquare_sg31970
import Theorems.Thm_OAI_UniversalTensorSquare_sg31971
import Theorems.Thm_OAI_UniversalTensorSquare_sg31972
import Theorems.Thm_OAI_UniversalTensorSquare_sg31973
import Theorems.Thm_OAI_UniversalTensorSquare_sg31974
import Theorems.Thm_OAI_UniversalTensorSquare_sg31975
import Theorems.Thm_OAI_UniversalTensorSquare_sg31976
import Theorems.Thm_OAI_UniversalTensorSquare_sg31977
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg796

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2925 : RowSquare [8,2,2,2] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3362 : RowSquare [6,4,3,2] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg796

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

lemma sg14813 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2925 sg3362

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31961 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15290 sg14813

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree58_0All_oai : degreeTree58_0.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31964,⟨sg31957,⟨sg31954,⟨sg31952,⟨sg31951,True.intro,True.intro⟩,⟨sg31953,True.intro,True.intro⟩⟩,⟨sg31956,⟨sg31955,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31961,⟨sg31959,⟨sg31958,True.intro,True.intro⟩,⟨sg31960,True.intro,True.intro⟩⟩,⟨sg31963,⟨sg31962,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg31971,⟨sg31968,⟨sg31966,⟨sg31965,True.intro,True.intro⟩,⟨sg31967,True.intro,True.intro⟩⟩,⟨sg31970,⟨sg31969,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31975,⟨sg31973,⟨sg31972,True.intro,True.intro⟩,⟨sg31974,True.intro,True.intro⟩⟩,⟨sg31977,⟨sg31976,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree58_0All_oai := @OAI.UniversalTensorSquare.degreeTree58_0All_oai
