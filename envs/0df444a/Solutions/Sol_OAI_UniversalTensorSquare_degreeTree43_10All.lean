-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_10All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T13:01:35.522718+00:00
-- url     : https://prove2.me/submissions/9f05b6ec-5321-4a01-b20d-d1585d132bb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_0All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_3All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_9All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10247
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg23691
import Theorems.Thm_OAI_UniversalTensorSquare_sg23692
import Theorems.Thm_OAI_UniversalTensorSquare_sg23693
import Theorems.Thm_OAI_UniversalTensorSquare_sg23694
import Theorems.Thm_OAI_UniversalTensorSquare_sg23695
import Theorems.Thm_OAI_UniversalTensorSquare_sg23696
import Theorems.Thm_OAI_UniversalTensorSquare_sg23697
import Theorems.Thm_OAI_UniversalTensorSquare_sg23698
import Theorems.Thm_OAI_UniversalTensorSquare_sg23699
import Theorems.Thm_OAI_UniversalTensorSquare_sg23700
import Theorems.Thm_OAI_UniversalTensorSquare_sg23701
import Theorems.Thm_OAI_UniversalTensorSquare_sg23703
import Theorems.Thm_OAI_UniversalTensorSquare_sg23704
import Theorems.Thm_OAI_UniversalTensorSquare_sg23705
import Theorems.Thm_OAI_UniversalTensorSquare_sg23706
import Theorems.Thm_OAI_UniversalTensorSquare_sg23707
import Theorems.Thm_OAI_UniversalTensorSquare_sg23739

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

lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [1,1,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10247

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

lemma degreeTree43_1All : degreeTree43_1.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23699,⟨sg23695,⟨sg23693,⟨sg23692,True.intro,True.intro⟩,⟨sg23694,True.intro,True.intro⟩⟩,⟨sg23697,⟨sg23696,True.intro,True.intro⟩,⟨sg23698,True.intro,True.intro⟩⟩⟩,⟨sg23703,⟨sg23701,⟨sg23700,True.intro,True.intro⟩,⟨sg23702,True.intro,True.intro⟩⟩,⟨sg23705,⟨sg23704,True.intro,True.intro⟩,⟨sg23706,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_2All : degreeTree43_2.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23691,degreeTree43_0All,degreeTree43_1All⟩

lemma degreeTree43_4All : degreeTree43_4.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23707,degreeTree43_2All,degreeTree43_3All⟩

lemma degreeTree43_10All_oai : degreeTree43_10.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23739,degreeTree43_4All,degreeTree43_9All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_10All_oai := @OAI.UniversalTensorSquare.degreeTree43_10All_oai
