-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_155All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:29:51.257071+00:00
-- url     : https://prove2.me/submissions/f78dc7fd-188a-46a7-a2c5-9103a8000eb5

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10293
import Theorems.Thm_OAI_UniversalTensorSquare_sg10295
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25677
import Theorems.Thm_OAI_UniversalTensorSquare_sg25678
import Theorems.Thm_OAI_UniversalTensorSquare_sg25679
import Theorems.Thm_OAI_UniversalTensorSquare_sg25680
import Theorems.Thm_OAI_UniversalTensorSquare_sg25681
import Theorems.Thm_OAI_UniversalTensorSquare_sg25682
import Theorems.Thm_OAI_UniversalTensorSquare_sg25683
import Theorems.Thm_OAI_UniversalTensorSquare_sg25684
import Theorems.Thm_OAI_UniversalTensorSquare_sg25685
import Theorems.Thm_OAI_UniversalTensorSquare_sg25686
import Theorems.Thm_OAI_UniversalTensorSquare_sg25687
import Theorems.Thm_OAI_UniversalTensorSquare_sg25688
import Theorems.Thm_OAI_UniversalTensorSquare_sg25689
import Theorems.Thm_OAI_UniversalTensorSquare_sg25690
import Theorems.Thm_OAI_UniversalTensorSquare_sg25691
import Theorems.Thm_OAI_UniversalTensorSquare_sg25693
import Theorems.Thm_OAI_UniversalTensorSquare_sg25694
import Theorems.Thm_OAI_UniversalTensorSquare_sg25695
import Theorems.Thm_OAI_UniversalTensorSquare_sg25696
import Theorems.Thm_OAI_UniversalTensorSquare_sg25697
import Theorems.Thm_OAI_UniversalTensorSquare_sg25698
import Theorems.Thm_OAI_UniversalTensorSquare_sg25699
import Theorems.Thm_OAI_UniversalTensorSquare_sg25700
import Theorems.Thm_OAI_UniversalTensorSquare_sg25701
import Theorems.Thm_OAI_UniversalTensorSquare_sg25702
import Theorems.Thm_OAI_UniversalTensorSquare_sg25703
import Theorems.Thm_OAI_UniversalTensorSquare_sg25704
import Theorems.Thm_OAI_UniversalTensorSquare_sg25706
import Theorems.Thm_OAI_UniversalTensorSquare_sg25707

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

lemma sg850 : RowSquare [4,3,2,1] [2,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1327

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

lemma sg25692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10293

lemma sg25705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10295

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

lemma degreeTree43_155All_oai : degreeTree43_155.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25692,⟨sg25684,⟨sg25680,⟨sg25678,⟨sg25677,True.intro,True.intro⟩,⟨sg25679,True.intro,True.intro⟩⟩,⟨sg25682,⟨sg25681,True.intro,True.intro⟩,⟨sg25683,True.intro,True.intro⟩⟩⟩,⟨sg25688,⟨sg25686,⟨sg25685,True.intro,True.intro⟩,⟨sg25687,True.intro,True.intro⟩⟩,⟨sg25690,⟨sg25689,True.intro,True.intro⟩,⟨sg25691,True.intro,True.intro⟩⟩⟩⟩,⟨sg25700,⟨sg25696,⟨sg25694,⟨sg25693,True.intro,True.intro⟩,⟨sg25695,True.intro,True.intro⟩⟩,⟨sg25698,⟨sg25697,True.intro,True.intro⟩,⟨sg25699,True.intro,True.intro⟩⟩⟩,⟨sg25704,⟨sg25702,⟨sg25701,True.intro,True.intro⟩,⟨sg25703,True.intro,True.intro⟩⟩,⟨sg25706,⟨sg25705,True.intro,True.intro⟩,⟨sg25707,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_155All_oai := @OAI.UniversalTensorSquare.degreeTree43_155All_oai
