-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_464All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:18:36.083197+00:00
-- url     : https://prove2.me/submissions/53e32ce2-dcab-4a49-869a-5f13f0106360

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg37161
import Theorems.Thm_OAI_UniversalTensorSquare_sg37162
import Theorems.Thm_OAI_UniversalTensorSquare_sg37163
import Theorems.Thm_OAI_UniversalTensorSquare_sg37164
import Theorems.Thm_OAI_UniversalTensorSquare_sg37165
import Theorems.Thm_OAI_UniversalTensorSquare_sg37166
import Theorems.Thm_OAI_UniversalTensorSquare_sg37167
import Theorems.Thm_OAI_UniversalTensorSquare_sg37168
import Theorems.Thm_OAI_UniversalTensorSquare_sg37169
import Theorems.Thm_OAI_UniversalTensorSquare_sg37171
import Theorems.Thm_OAI_UniversalTensorSquare_sg37172
import Theorems.Thm_OAI_UniversalTensorSquare_sg37173
import Theorems.Thm_OAI_UniversalTensorSquare_sg37174
import Theorems.Thm_OAI_UniversalTensorSquare_sg37175
import Theorems.Thm_OAI_UniversalTensorSquare_sg37176
import Theorems.Thm_OAI_UniversalTensorSquare_sg37177
import Theorems.Thm_OAI_UniversalTensorSquare_sg37178
import Theorems.Thm_OAI_UniversalTensorSquare_sg37179
import Theorems.Thm_OAI_UniversalTensorSquare_sg37180
import Theorems.Thm_OAI_UniversalTensorSquare_sg37181
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1131 : RowSquare [2,2,2,2,2,1] [3,3,3,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1094 : RowSquare [7,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg372

end UniversalTensorSquare
end
end

end OAI
end

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6710 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1094

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18470 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6710

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 91. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37170 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18470

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

lemma degreeTree62_464All_oai : degreeTree62_464.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37171,⟨sg37166,⟨sg37163,⟨sg37162,⟨sg37161,True.intro,True.intro⟩,True.intro⟩,⟨sg37165,⟨sg37164,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37169,⟨sg37168,⟨sg37167,True.intro,True.intro⟩,True.intro⟩,⟨sg37170,True.intro,True.intro⟩⟩⟩,⟨sg37177,⟨sg37174,⟨sg37173,⟨sg37172,True.intro,True.intro⟩,True.intro⟩,⟨sg37176,⟨sg37175,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37180,⟨sg37179,⟨sg37178,True.intro,True.intro⟩,True.intro⟩,⟨sg37181,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_464All_oai := @OAI.UniversalTensorSquare.degreeTree62_464All_oai
