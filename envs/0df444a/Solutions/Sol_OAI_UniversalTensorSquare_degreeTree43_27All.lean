-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_27All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:05.331443+00:00
-- url     : https://prove2.me/submissions/f70172ad-0cbb-4dd5-ad50-441ba1ca46e7

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10090
import Theorems.Thm_OAI_UniversalTensorSquare_sg10108
import Theorems.Thm_OAI_UniversalTensorSquare_sg10218
import Theorems.Thm_OAI_UniversalTensorSquare_sg10219
import Theorems.Thm_OAI_UniversalTensorSquare_sg10220
import Theorems.Thm_OAI_UniversalTensorSquare_sg10221
import Theorems.Thm_OAI_UniversalTensorSquare_sg10297
import Theorems.Thm_OAI_UniversalTensorSquare_sg10298
import Theorems.Thm_OAI_UniversalTensorSquare_sg10601
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg24031
import Theorems.Thm_OAI_UniversalTensorSquare_sg24032
import Theorems.Thm_OAI_UniversalTensorSquare_sg24034
import Theorems.Thm_OAI_UniversalTensorSquare_sg24035
import Theorems.Thm_OAI_UniversalTensorSquare_sg24036
import Theorems.Thm_OAI_UniversalTensorSquare_sg24038
import Theorems.Thm_OAI_UniversalTensorSquare_sg24039
import Theorems.Thm_OAI_UniversalTensorSquare_sg24040
import Theorems.Thm_OAI_UniversalTensorSquare_sg24041
import Theorems.Thm_OAI_UniversalTensorSquare_sg24043
import Theorems.Thm_OAI_UniversalTensorSquare_sg24044
import Theorems.Thm_OAI_UniversalTensorSquare_sg24047
import Theorems.Thm_OAI_UniversalTensorSquare_sg24048
import Theorems.Thm_OAI_UniversalTensorSquare_sg24049
import Theorems.Thm_OAI_UniversalTensorSquare_sg24051
import Theorems.Thm_OAI_UniversalTensorSquare_sg24052
import Theorems.Thm_OAI_UniversalTensorSquare_sg24053
import Theorems.Thm_OAI_UniversalTensorSquare_sg24054
import Theorems.Thm_OAI_UniversalTensorSquare_sg24055
import Theorems.Thm_OAI_UniversalTensorSquare_sg24058
import Theorems.Thm_OAI_UniversalTensorSquare_sg24059
import Theorems.Thm_OAI_UniversalTensorSquare_sg24060
import Theorems.Thm_OAI_UniversalTensorSquare_sg54
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8532

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

lemma sg77 : RowSquare [3,2,1] [2,2,2] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,2])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,2]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,2]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2])) he) hh

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

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

lemma sg1691 : RowSquare [5,3,2,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg54

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8368 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg1691

lemma sg8524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1327

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

lemma sg24033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10218

lemma sg24037 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10219

lemma sg24042 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10297

lemma sg24045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10220

lemma sg24046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10298

lemma sg24050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10221

lemma sg24056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8368 sg10601

lemma sg24057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10108

lemma sg24061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10090

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

lemma degreeTree43_27All_oai : degreeTree43_27.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24046,⟨sg24038,⟨sg24034,⟨sg24032,⟨sg24031,True.intro,True.intro⟩,⟨sg24033,True.intro,True.intro⟩⟩,⟨sg24036,⟨sg24035,True.intro,True.intro⟩,⟨sg24037,True.intro,True.intro⟩⟩⟩,⟨sg24042,⟨sg24040,⟨sg24039,True.intro,True.intro⟩,⟨sg24041,True.intro,True.intro⟩⟩,⟨sg24044,⟨sg24043,True.intro,True.intro⟩,⟨sg24045,True.intro,True.intro⟩⟩⟩⟩,⟨sg24054,⟨sg24050,⟨sg24048,⟨sg24047,True.intro,True.intro⟩,⟨sg24049,True.intro,True.intro⟩⟩,⟨sg24052,⟨sg24051,True.intro,True.intro⟩,⟨sg24053,True.intro,True.intro⟩⟩⟩,⟨sg24058,⟨sg24056,⟨sg24055,True.intro,True.intro⟩,⟨sg24057,True.intro,True.intro⟩⟩,⟨sg24060,⟨sg24059,True.intro,True.intro⟩,⟨sg24061,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_27All_oai := @OAI.UniversalTensorSquare.degreeTree43_27All_oai
