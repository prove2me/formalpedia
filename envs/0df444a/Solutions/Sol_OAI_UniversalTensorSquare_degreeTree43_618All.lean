-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_618All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:54:43.820442+00:00
-- url     : https://prove2.me/submissions/9e10bf3c-cb2f-4ff9-a140-b2a5ed011bfc

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10006
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg31582
import Theorems.Thm_OAI_UniversalTensorSquare_sg31583
import Theorems.Thm_OAI_UniversalTensorSquare_sg31584
import Theorems.Thm_OAI_UniversalTensorSquare_sg31586
import Theorems.Thm_OAI_UniversalTensorSquare_sg31589
import Theorems.Thm_OAI_UniversalTensorSquare_sg31590
import Theorems.Thm_OAI_UniversalTensorSquare_sg31591
import Theorems.Thm_OAI_UniversalTensorSquare_sg31592
import Theorems.Thm_OAI_UniversalTensorSquare_sg31593
import Theorems.Thm_OAI_UniversalTensorSquare_sg31594
import Theorems.Thm_OAI_UniversalTensorSquare_sg31595
import Theorems.Thm_OAI_UniversalTensorSquare_sg31596
import Theorems.Thm_OAI_UniversalTensorSquare_sg31601
import Theorems.Thm_OAI_UniversalTensorSquare_sg31602
import Theorems.Thm_OAI_UniversalTensorSquare_sg31604
import Theorems.Thm_OAI_UniversalTensorSquare_sg31605
import Theorems.Thm_OAI_UniversalTensorSquare_sg31606
import Theorems.Thm_OAI_UniversalTensorSquare_sg31607
import Theorems.Thm_OAI_UniversalTensorSquare_sg31608
import Theorems.Thm_OAI_UniversalTensorSquare_sg31610
import Theorems.Thm_OAI_UniversalTensorSquare_sg31611
import Theorems.Thm_OAI_UniversalTensorSquare_sg31612
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg9358
import Theorems.Thm_OAI_UniversalTensorSquare_sg9359
import Theorems.Thm_OAI_UniversalTensorSquare_sg9384

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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg74 : RowSquare [3,2,1] [1,1,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [1,1,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1])) he) hh

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

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg133 : RowSquare [3,1,1,1,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg88

lemma sg272 : RowSquare [3,2,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg74

lemma sg273 : RowSquare [3,2,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg32

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

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

lemma sg698 : RowSquare [6,2,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg32

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

lemma sg1908 : RowSquare [7,3,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg373

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5089 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg698

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7780 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1754

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

lemma sg6605 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg1908

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

lemma sg10005 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5089

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

lemma sg8795 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg2251

lemma sg8799 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg2702

lemma sg8800 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg2251

lemma sg8801 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7780

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11543 : RowSquare [8,6,2,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg4345

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10005

lemma sg31587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10006

lemma sg31588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6605 sg11543

lemma sg31597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9358

lemma sg31598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9359

lemma sg31599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9359

lemma sg31600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg10006

lemma sg31603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,9,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9384

lemma sg31609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9384

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

lemma degreeTree43_618All_oai : degreeTree43_618.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31597,⟨sg31589,⟨sg31585,⟨sg31583,⟨sg31582,True.intro,True.intro⟩,⟨sg31584,True.intro,True.intro⟩⟩,⟨sg31587,⟨sg31586,True.intro,True.intro⟩,⟨sg31588,True.intro,True.intro⟩⟩⟩,⟨sg31593,⟨sg31591,⟨sg31590,True.intro,True.intro⟩,⟨sg31592,True.intro,True.intro⟩⟩,⟨sg31595,⟨sg31594,True.intro,True.intro⟩,⟨sg31596,True.intro,True.intro⟩⟩⟩⟩,⟨sg31605,⟨sg31601,⟨sg31599,⟨sg31598,True.intro,True.intro⟩,⟨sg31600,True.intro,True.intro⟩⟩,⟨sg31603,⟨sg31602,True.intro,True.intro⟩,⟨sg31604,True.intro,True.intro⟩⟩⟩,⟨sg31609,⟨sg31607,⟨sg31606,True.intro,True.intro⟩,⟨sg31608,True.intro,True.intro⟩⟩,⟨sg31611,⟨sg31610,True.intro,True.intro⟩,⟨sg31612,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_618All_oai := @OAI.UniversalTensorSquare.degreeTree43_618All_oai
