-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_117All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:16.916242+00:00
-- url     : https://prove2.me/submissions/ecdd9ec5-816c-45c3-a053-c81ad415164b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25193
import Theorems.Thm_OAI_UniversalTensorSquare_sg25194
import Theorems.Thm_OAI_UniversalTensorSquare_sg25195
import Theorems.Thm_OAI_UniversalTensorSquare_sg25196
import Theorems.Thm_OAI_UniversalTensorSquare_sg25197
import Theorems.Thm_OAI_UniversalTensorSquare_sg25198
import Theorems.Thm_OAI_UniversalTensorSquare_sg25199
import Theorems.Thm_OAI_UniversalTensorSquare_sg25200
import Theorems.Thm_OAI_UniversalTensorSquare_sg25201
import Theorems.Thm_OAI_UniversalTensorSquare_sg25202
import Theorems.Thm_OAI_UniversalTensorSquare_sg25203
import Theorems.Thm_OAI_UniversalTensorSquare_sg25205
import Theorems.Thm_OAI_UniversalTensorSquare_sg25206
import Theorems.Thm_OAI_UniversalTensorSquare_sg25207
import Theorems.Thm_OAI_UniversalTensorSquare_sg25208
import Theorems.Thm_OAI_UniversalTensorSquare_sg25209
import Theorems.Thm_OAI_UniversalTensorSquare_sg25210
import Theorems.Thm_OAI_UniversalTensorSquare_sg25211
import Theorems.Thm_OAI_UniversalTensorSquare_sg25212
import Theorems.Thm_OAI_UniversalTensorSquare_sg25213
import Theorems.Thm_OAI_UniversalTensorSquare_sg25214
import Theorems.Thm_OAI_UniversalTensorSquare_sg25215
import Theorems.Thm_OAI_UniversalTensorSquare_sg25216
import Theorems.Thm_OAI_UniversalTensorSquare_sg25217
import Theorems.Thm_OAI_UniversalTensorSquare_sg25218
import Theorems.Thm_OAI_UniversalTensorSquare_sg25219
import Theorems.Thm_OAI_UniversalTensorSquare_sg25220
import Theorems.Thm_OAI_UniversalTensorSquare_sg25221
import Theorems.Thm_OAI_UniversalTensorSquare_sg25222
import Theorems.Thm_OAI_UniversalTensorSquare_sg25223
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg9520

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9520

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

lemma degreeTree43_117All_oai : degreeTree43_117.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25208,⟨sg25200,⟨sg25196,⟨sg25194,⟨sg25193,True.intro,True.intro⟩,⟨sg25195,True.intro,True.intro⟩⟩,⟨sg25198,⟨sg25197,True.intro,True.intro⟩,⟨sg25199,True.intro,True.intro⟩⟩⟩,⟨sg25204,⟨sg25202,⟨sg25201,True.intro,True.intro⟩,⟨sg25203,True.intro,True.intro⟩⟩,⟨sg25206,⟨sg25205,True.intro,True.intro⟩,⟨sg25207,True.intro,True.intro⟩⟩⟩⟩,⟨sg25216,⟨sg25212,⟨sg25210,⟨sg25209,True.intro,True.intro⟩,⟨sg25211,True.intro,True.intro⟩⟩,⟨sg25214,⟨sg25213,True.intro,True.intro⟩,⟨sg25215,True.intro,True.intro⟩⟩⟩,⟨sg25220,⟨sg25218,⟨sg25217,True.intro,True.intro⟩,⟨sg25219,True.intro,True.intro⟩⟩,⟨sg25222,⟨sg25221,True.intro,True.intro⟩,⟨sg25223,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_117All_oai := @OAI.UniversalTensorSquare.degreeTree43_117All_oai
