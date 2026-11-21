-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_224All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:37.777756+00:00
-- url     : https://prove2.me/submissions/cab11fe9-0248-4ceb-be20-24eee0a57fd3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10108
import Theorems.Thm_OAI_UniversalTensorSquare_sg10297
import Theorems.Thm_OAI_UniversalTensorSquare_sg10298
import Theorems.Thm_OAI_UniversalTensorSquare_sg10689
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg26533
import Theorems.Thm_OAI_UniversalTensorSquare_sg26534
import Theorems.Thm_OAI_UniversalTensorSquare_sg26536
import Theorems.Thm_OAI_UniversalTensorSquare_sg26541
import Theorems.Thm_OAI_UniversalTensorSquare_sg26543
import Theorems.Thm_OAI_UniversalTensorSquare_sg26544
import Theorems.Thm_OAI_UniversalTensorSquare_sg26545
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg541
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg814
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8538
import Theorems.Thm_OAI_UniversalTensorSquare_sg9493
import Theorems.Thm_OAI_UniversalTensorSquare_sg9562
import Theorems.Thm_OAI_UniversalTensorSquare_sg9727

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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg8657 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1754

lemma sg8658 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1755

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8736 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10297

lemma sg26537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9562

lemma sg26538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10298

lemma sg26539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10689

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10108

lemma sg26542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9727

lemma sg26546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9493

lemma sg26547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9727

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

lemma degreeTree43_224All_oai : degreeTree43_224.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26540,⟨sg26536,⟨sg26534,⟨sg26533,True.intro,True.intro⟩,⟨sg26535,True.intro,True.intro⟩⟩,⟨sg26538,⟨sg26537,True.intro,True.intro⟩,⟨sg26539,True.intro,True.intro⟩⟩⟩,⟨sg26544,⟨sg26542,⟨sg26541,True.intro,True.intro⟩,⟨sg26543,True.intro,True.intro⟩⟩,⟨sg26546,⟨sg26545,True.intro,True.intro⟩,⟨sg26547,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_224All_oai := @OAI.UniversalTensorSquare.degreeTree43_224All_oai
