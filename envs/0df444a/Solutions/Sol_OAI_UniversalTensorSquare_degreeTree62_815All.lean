-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_815All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:25:38.351001+00:00
-- url     : https://prove2.me/submissions/2978d362-64ef-4905-b102-ef8e42861305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg18748
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg40998
import Theorems.Thm_OAI_UniversalTensorSquare_sg40999
import Theorems.Thm_OAI_UniversalTensorSquare_sg41000
import Theorems.Thm_OAI_UniversalTensorSquare_sg41001
import Theorems.Thm_OAI_UniversalTensorSquare_sg41002
import Theorems.Thm_OAI_UniversalTensorSquare_sg41003
import Theorems.Thm_OAI_UniversalTensorSquare_sg41004
import Theorems.Thm_OAI_UniversalTensorSquare_sg41005
import Theorems.Thm_OAI_UniversalTensorSquare_sg41006
import Theorems.Thm_OAI_UniversalTensorSquare_sg41007
import Theorems.Thm_OAI_UniversalTensorSquare_sg41008
import Theorems.Thm_OAI_UniversalTensorSquare_sg41009
import Theorems.Thm_OAI_UniversalTensorSquare_sg41010
import Theorems.Thm_OAI_UniversalTensorSquare_sg41012
import Theorems.Thm_OAI_UniversalTensorSquare_sg41013
import Theorems.Thm_OAI_UniversalTensorSquare_sg41014
import Theorems.Thm_OAI_UniversalTensorSquare_sg41015
import Theorems.Thm_OAI_UniversalTensorSquare_sg41016
import Theorems.Thm_OAI_UniversalTensorSquare_sg41017
import Theorems.Thm_OAI_UniversalTensorSquare_sg41018
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1625 : RowSquare [4,2,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg383

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5741 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg1625

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20318 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5741

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 101. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41011 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,8,7,5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18748

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

lemma degreeTree62_815All_oai : degreeTree62_815.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41008,⟨sg41003,⟨sg41000,⟨sg40999,⟨sg40998,True.intro,True.intro⟩,True.intro⟩,⟨sg41002,⟨sg41001,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41006,⟨sg41005,⟨sg41004,True.intro,True.intro⟩,True.intro⟩,⟨sg41007,True.intro,True.intro⟩⟩⟩,⟨sg41014,⟨sg41011,⟨sg41010,⟨sg41009,True.intro,True.intro⟩,True.intro⟩,⟨sg41013,⟨sg41012,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41017,⟨sg41016,⟨sg41015,True.intro,True.intro⟩,True.intro⟩,⟨sg41018,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_815All_oai := @OAI.UniversalTensorSquare.degreeTree62_815All_oai
