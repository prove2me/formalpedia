-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_566All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:31:33.990818+00:00
-- url     : https://prove2.me/submissions/a269db7f-d361-43c8-9bc5-122e75d7aaf1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_565All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg19936
import Theorems.Thm_OAI_UniversalTensorSquare_sg23
import Theorems.Thm_OAI_UniversalTensorSquare_sg38235
import Theorems.Thm_OAI_UniversalTensorSquare_sg38236
import Theorems.Thm_OAI_UniversalTensorSquare_sg38237
import Theorems.Thm_OAI_UniversalTensorSquare_sg38238
import Theorems.Thm_OAI_UniversalTensorSquare_sg38239
import Theorems.Thm_OAI_UniversalTensorSquare_sg38240
import Theorems.Thm_OAI_UniversalTensorSquare_sg38241
import Theorems.Thm_OAI_UniversalTensorSquare_sg38242
import Theorems.Thm_OAI_UniversalTensorSquare_sg38243
import Theorems.Thm_OAI_UniversalTensorSquare_sg38244
import Theorems.Thm_OAI_UniversalTensorSquare_sg38245
import Theorems.Thm_OAI_UniversalTensorSquare_sg38246
import Theorems.Thm_OAI_UniversalTensorSquare_sg38247
import Theorems.Thm_OAI_UniversalTensorSquare_sg38248
import Theorems.Thm_OAI_UniversalTensorSquare_sg38249
import Theorems.Thm_OAI_UniversalTensorSquare_sg38250
import Theorems.Thm_OAI_UniversalTensorSquare_sg38251
import Theorems.Thm_OAI_UniversalTensorSquare_sg38252
import Theorems.Thm_OAI_UniversalTensorSquare_sg38253
import Theorems.Thm_OAI_UniversalTensorSquare_sg38254
import Theorems.Thm_OAI_UniversalTensorSquare_sg44
import Theorems.Thm_OAI_UniversalTensorSquare_sg46

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

lemma sg632 : RowSquare [5,2,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg23

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

lemma sg729 : RowSquare [2,2,2,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg44

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg6468 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg729

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18909 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6468

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 94. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38255 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,8,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19936

lemma sg38256 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,8,8,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19936

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

lemma degreeTree62_564All : degreeTree62_564.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38245,⟨sg38240,⟨sg38237,⟨sg38236,⟨sg38235,True.intro,True.intro⟩,True.intro⟩,⟨sg38239,⟨sg38238,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38243,⟨sg38242,⟨sg38241,True.intro,True.intro⟩,True.intro⟩,⟨sg38244,True.intro,True.intro⟩⟩⟩,⟨sg38251,⟨sg38248,⟨sg38247,⟨sg38246,True.intro,True.intro⟩,True.intro⟩,⟨sg38250,⟨sg38249,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38254,⟨sg38253,⟨sg38252,True.intro,True.intro⟩,True.intro⟩,⟨sg38255,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_566All_oai : degreeTree62_566.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38256,degreeTree62_564All,degreeTree62_565All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_566All_oai := @OAI.UniversalTensorSquare.degreeTree62_566All_oai
