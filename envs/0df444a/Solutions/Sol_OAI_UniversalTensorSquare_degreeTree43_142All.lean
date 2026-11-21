-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_142All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:42:23.344204+00:00
-- url     : https://prove2.me/submissions/4b1c5322-a120-44f0-91c8-ce3d5b060226

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg25500
import Theorems.Thm_OAI_UniversalTensorSquare_sg25501
import Theorems.Thm_OAI_UniversalTensorSquare_sg25502
import Theorems.Thm_OAI_UniversalTensorSquare_sg25503
import Theorems.Thm_OAI_UniversalTensorSquare_sg25504
import Theorems.Thm_OAI_UniversalTensorSquare_sg25505
import Theorems.Thm_OAI_UniversalTensorSquare_sg25506
import Theorems.Thm_OAI_UniversalTensorSquare_sg25507
import Theorems.Thm_OAI_UniversalTensorSquare_sg25508
import Theorems.Thm_OAI_UniversalTensorSquare_sg25509
import Theorems.Thm_OAI_UniversalTensorSquare_sg25510
import Theorems.Thm_OAI_UniversalTensorSquare_sg25511
import Theorems.Thm_OAI_UniversalTensorSquare_sg25513
import Theorems.Thm_OAI_UniversalTensorSquare_sg25514
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg8484

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

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

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

lemma sg1328 : RowSquare [6,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg112

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10174 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1328 sg1328

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8484 sg10174

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

lemma degreeTree43_142All_oai : degreeTree43_142.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25507,⟨sg25503,⟨sg25501,⟨sg25500,True.intro,True.intro⟩,⟨sg25502,True.intro,True.intro⟩⟩,⟨sg25505,⟨sg25504,True.intro,True.intro⟩,⟨sg25506,True.intro,True.intro⟩⟩⟩,⟨sg25511,⟨sg25509,⟨sg25508,True.intro,True.intro⟩,⟨sg25510,True.intro,True.intro⟩⟩,⟨sg25513,⟨sg25512,True.intro,True.intro⟩,⟨sg25514,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_142All_oai := @OAI.UniversalTensorSquare.degreeTree43_142All_oai
