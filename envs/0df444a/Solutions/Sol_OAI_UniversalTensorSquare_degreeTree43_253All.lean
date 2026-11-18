-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_253All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:38.713473+00:00
-- url     : https://prove2.me/submissions/02d7d768-14a8-45b2-a1d6-9a7edf7530c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg26905
import Theorems.Thm_OAI_UniversalTensorSquare_sg26908
import Theorems.Thm_OAI_UniversalTensorSquare_sg26910
import Theorems.Thm_OAI_UniversalTensorSquare_sg26911
import Theorems.Thm_OAI_UniversalTensorSquare_sg26912
import Theorems.Thm_OAI_UniversalTensorSquare_sg26913
import Theorems.Thm_OAI_UniversalTensorSquare_sg26914
import Theorems.Thm_OAI_UniversalTensorSquare_sg26916
import Theorems.Thm_OAI_UniversalTensorSquare_sg26917
import Theorems.Thm_OAI_UniversalTensorSquare_sg26918
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg9839
import Theorems.Thm_OAI_UniversalTensorSquare_sg9842
import Theorems.Thm_OAI_UniversalTensorSquare_sg9843
import Theorems.Thm_OAI_UniversalTensorSquare_sg9873

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

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

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

lemma sg134 : RowSquare [3,1,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

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

lemma sg813 : RowSquare [4,2,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

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

lemma sg1426 : RowSquare [6,3,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg181

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

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

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

lemma sg9228 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1001 sg1782

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8733 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg813 sg1327

lemma sg8805 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg2702

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

lemma sg9522 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1426

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

lemma sg26903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9873

lemma sg26904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9228

lemma sg26906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9839

lemma sg26907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9522

lemma sg26909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9842

lemma sg26915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9843

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

lemma degreeTree43_253All_oai : degreeTree43_253.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26911,⟨sg26907,⟨sg26905,⟨sg26904,⟨sg26903,True.intro,True.intro⟩,True.intro⟩,⟨sg26906,True.intro,True.intro⟩⟩,⟨sg26909,⟨sg26908,True.intro,True.intro⟩,⟨sg26910,True.intro,True.intro⟩⟩⟩,⟨sg26915,⟨sg26913,⟨sg26912,True.intro,True.intro⟩,⟨sg26914,True.intro,True.intro⟩⟩,⟨sg26917,⟨sg26916,True.intro,True.intro⟩,⟨sg26918,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_253All_oai := @OAI.UniversalTensorSquare.degreeTree43_253All_oai
