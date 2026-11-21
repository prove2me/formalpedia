-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_33All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:06:38.157546+00:00
-- url     : https://prove2.me/submissions/ac396453-70f9-413b-b336-73f584565d11

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10219
import Theorems.Thm_OAI_UniversalTensorSquare_sg10221
import Theorems.Thm_OAI_UniversalTensorSquare_sg10223
import Theorems.Thm_OAI_UniversalTensorSquare_sg10224
import Theorems.Thm_OAI_UniversalTensorSquare_sg10225
import Theorems.Thm_OAI_UniversalTensorSquare_sg10226
import Theorems.Thm_OAI_UniversalTensorSquare_sg10240
import Theorems.Thm_OAI_UniversalTensorSquare_sg10242
import Theorems.Thm_OAI_UniversalTensorSquare_sg10302
import Theorems.Thm_OAI_UniversalTensorSquare_sg10303
import Theorems.Thm_OAI_UniversalTensorSquare_sg10304
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg24099
import Theorems.Thm_OAI_UniversalTensorSquare_sg24100
import Theorems.Thm_OAI_UniversalTensorSquare_sg24102
import Theorems.Thm_OAI_UniversalTensorSquare_sg24103
import Theorems.Thm_OAI_UniversalTensorSquare_sg24104
import Theorems.Thm_OAI_UniversalTensorSquare_sg24106
import Theorems.Thm_OAI_UniversalTensorSquare_sg24107
import Theorems.Thm_OAI_UniversalTensorSquare_sg24110
import Theorems.Thm_OAI_UniversalTensorSquare_sg24111
import Theorems.Thm_OAI_UniversalTensorSquare_sg24114
import Theorems.Thm_OAI_UniversalTensorSquare_sg24115
import Theorems.Thm_OAI_UniversalTensorSquare_sg24116
import Theorems.Thm_OAI_UniversalTensorSquare_sg24118
import Theorems.Thm_OAI_UniversalTensorSquare_sg24121
import Theorems.Thm_OAI_UniversalTensorSquare_sg24126
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9023
import Theorems.Thm_OAI_UniversalTensorSquare_sg9476
import Theorems.Thm_OAI_UniversalTensorSquare_sg9479
import Theorems.Thm_OAI_UniversalTensorSquare_sg9748

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

lemma sg4 : RowSquare [2,1] [1,1,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [1,1,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [1,1,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [1,1,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1])) he) hh

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

lemma sg807 : RowSquare [4,2,1,1,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5525 : RowSquare [5,5,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg586

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

lemma sg8720 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1327

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8860 : RowSquare [7,6,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5525

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg24096 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9476

lemma sg24097 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10302

lemma sg24098 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10240

lemma sg24101 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10303

lemma sg24105 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10223

lemma sg24108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10224

lemma sg24109 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10219

lemma sg24112 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9476

lemma sg24113 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10304

lemma sg24117 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10225

lemma sg24119 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10242

lemma sg24120 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9748

lemma sg24122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10226

lemma sg24123 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10221

lemma sg24124 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9023

lemma sg24125 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9479

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

lemma degreeTree43_33All_oai : degreeTree43_33.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24111,⟨sg24103,⟨sg24099,⟨sg24097,⟨sg24096,True.intro,True.intro⟩,⟨sg24098,True.intro,True.intro⟩⟩,⟨sg24101,⟨sg24100,True.intro,True.intro⟩,⟨sg24102,True.intro,True.intro⟩⟩⟩,⟨sg24107,⟨sg24105,⟨sg24104,True.intro,True.intro⟩,⟨sg24106,True.intro,True.intro⟩⟩,⟨sg24109,⟨sg24108,True.intro,True.intro⟩,⟨sg24110,True.intro,True.intro⟩⟩⟩⟩,⟨sg24119,⟨sg24115,⟨sg24113,⟨sg24112,True.intro,True.intro⟩,⟨sg24114,True.intro,True.intro⟩⟩,⟨sg24117,⟨sg24116,True.intro,True.intro⟩,⟨sg24118,True.intro,True.intro⟩⟩⟩,⟨sg24123,⟨sg24121,⟨sg24120,True.intro,True.intro⟩,⟨sg24122,True.intro,True.intro⟩⟩,⟨sg24125,⟨sg24124,True.intro,True.intro⟩,⟨sg24126,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_33All_oai := @OAI.UniversalTensorSquare.degreeTree43_33All_oai
