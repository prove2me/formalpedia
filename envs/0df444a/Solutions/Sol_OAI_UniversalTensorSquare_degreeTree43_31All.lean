-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_31All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:46.271576+00:00
-- url     : https://prove2.me/submissions/7f6190f9-7f69-4048-8652-0d1787db9bb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10215
import Theorems.Thm_OAI_UniversalTensorSquare_sg10222
import Theorems.Thm_OAI_UniversalTensorSquare_sg10300
import Theorems.Thm_OAI_UniversalTensorSquare_sg10301
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1423
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg24082
import Theorems.Thm_OAI_UniversalTensorSquare_sg24083
import Theorems.Thm_OAI_UniversalTensorSquare_sg24084
import Theorems.Thm_OAI_UniversalTensorSquare_sg24085
import Theorems.Thm_OAI_UniversalTensorSquare_sg24087
import Theorems.Thm_OAI_UniversalTensorSquare_sg24091
import Theorems.Thm_OAI_UniversalTensorSquare_sg24092
import Theorems.Thm_OAI_UniversalTensorSquare_sg24094
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8730
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg27 : RowSquare [2,2,1] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg264 : RowSquare [3,1,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg7 sg34

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

lemma sg1764 : RowSquare [6,2,1,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg264

lemma sg1798 : RowSquare [6,3,2,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg178

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9018 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1798

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9743 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1764

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

lemma sg8860 : RowSquare [7,6,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5525

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9452 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1423

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

lemma sg24080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9452

lemma sg24081 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10300

lemma sg24086 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9743

lemma sg24088 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10222

lemma sg24089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9018

lemma sg24090 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10215

lemma sg24093 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10301

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

lemma degreeTree43_31All_oai : degreeTree43_31.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24087,⟨sg24083,⟨sg24081,⟨sg24080,True.intro,True.intro⟩,⟨sg24082,True.intro,True.intro⟩⟩,⟨sg24085,⟨sg24084,True.intro,True.intro⟩,⟨sg24086,True.intro,True.intro⟩⟩⟩,⟨sg24091,⟨sg24089,⟨sg24088,True.intro,True.intro⟩,⟨sg24090,True.intro,True.intro⟩⟩,⟨sg24093,⟨sg24092,True.intro,True.intro⟩,⟨sg24094,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_31All_oai := @OAI.UniversalTensorSquare.degreeTree43_31All_oai
