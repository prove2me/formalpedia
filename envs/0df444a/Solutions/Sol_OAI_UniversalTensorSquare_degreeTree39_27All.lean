-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_27All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:26:33.834432+00:00
-- url     : https://prove2.me/submissions/20751674-7f35-44d9-8d31-dfc395d14450

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_25All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg22106
import Theorems.Thm_OAI_UniversalTensorSquare_sg22108
import Theorems.Thm_OAI_UniversalTensorSquare_sg22109
import Theorems.Thm_OAI_UniversalTensorSquare_sg22110
import Theorems.Thm_OAI_UniversalTensorSquare_sg22111
import Theorems.Thm_OAI_UniversalTensorSquare_sg22112
import Theorems.Thm_OAI_UniversalTensorSquare_sg22113
import Theorems.Thm_OAI_UniversalTensorSquare_sg22114
import Theorems.Thm_OAI_UniversalTensorSquare_sg22115
import Theorems.Thm_OAI_UniversalTensorSquare_sg22116
import Theorems.Thm_OAI_UniversalTensorSquare_sg22117
import Theorems.Thm_OAI_UniversalTensorSquare_sg22118
import Theorems.Thm_OAI_UniversalTensorSquare_sg22119
import Theorems.Thm_OAI_UniversalTensorSquare_sg22120
import Theorems.Thm_OAI_UniversalTensorSquare_sg22121
import Theorems.Thm_OAI_UniversalTensorSquare_sg22122
import Theorems.Thm_OAI_UniversalTensorSquare_sg22123
import Theorems.Thm_OAI_UniversalTensorSquare_sg22124
import Theorems.Thm_OAI_UniversalTensorSquare_sg22125
import Theorems.Thm_OAI_UniversalTensorSquare_sg22126
import Theorems.Thm_OAI_UniversalTensorSquare_sg22127
import Theorems.Thm_OAI_UniversalTensorSquare_sg22128
import Theorems.Thm_OAI_UniversalTensorSquare_sg22129
import Theorems.Thm_OAI_UniversalTensorSquare_sg22130
import Theorems.Thm_OAI_UniversalTensorSquare_sg22131
import Theorems.Thm_OAI_UniversalTensorSquare_sg22132
import Theorems.Thm_OAI_UniversalTensorSquare_sg22133
import Theorems.Thm_OAI_UniversalTensorSquare_sg22134
import Theorems.Thm_OAI_UniversalTensorSquare_sg6151
import Theorems.Thm_OAI_UniversalTensorSquare_sg7609

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

lemma sg22107 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7609

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

lemma degreeTree39_26All : degreeTree39_26.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22121,⟨sg22114,⟨sg22110,⟨sg22108,⟨sg22107,True.intro,True.intro⟩,⟨sg22109,True.intro,True.intro⟩⟩,⟨sg22112,⟨sg22111,True.intro,True.intro⟩,⟨sg22113,True.intro,True.intro⟩⟩⟩,⟨sg22118,⟨sg22116,⟨sg22115,True.intro,True.intro⟩,⟨sg22117,True.intro,True.intro⟩⟩,⟨sg22120,⟨sg22119,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22128,⟨sg22125,⟨sg22123,⟨sg22122,True.intro,True.intro⟩,⟨sg22124,True.intro,True.intro⟩⟩,⟨sg22127,⟨sg22126,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22132,⟨sg22130,⟨sg22129,True.intro,True.intro⟩,⟨sg22131,True.intro,True.intro⟩⟩,⟨sg22134,⟨sg22133,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_27All_oai : degreeTree39_27.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22106,degreeTree39_25All,degreeTree39_26All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_27All_oai := @OAI.UniversalTensorSquare.degreeTree39_27All_oai
