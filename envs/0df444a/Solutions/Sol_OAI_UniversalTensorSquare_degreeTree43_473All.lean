-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_473All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:46.502142+00:00
-- url     : https://prove2.me/submissions/26f24703-221f-4749-bb2a-831c3408c1f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10351
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg29742
import Theorems.Thm_OAI_UniversalTensorSquare_sg29744
import Theorems.Thm_OAI_UniversalTensorSquare_sg29745
import Theorems.Thm_OAI_UniversalTensorSquare_sg29746
import Theorems.Thm_OAI_UniversalTensorSquare_sg29749
import Theorems.Thm_OAI_UniversalTensorSquare_sg29750
import Theorems.Thm_OAI_UniversalTensorSquare_sg29753
import Theorems.Thm_OAI_UniversalTensorSquare_sg29754
import Theorems.Thm_OAI_UniversalTensorSquare_sg29755
import Theorems.Thm_OAI_UniversalTensorSquare_sg29756
import Theorems.Thm_OAI_UniversalTensorSquare_sg29757
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg9259
import Theorems.Thm_OAI_UniversalTensorSquare_sg9282
import Theorems.Thm_OAI_UniversalTensorSquare_sg9605

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

lemma sg272 : RowSquare [3,2,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg74

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

lemma sg7781 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1327

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8795 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg2251

lemma sg8801 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7780

lemma sg8802 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7781

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 73. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9282

lemma sg29747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9259

lemma sg29748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9259

lemma sg29751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9605

lemma sg29752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10351

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

lemma degreeTree43_473All_oai : degreeTree43_473.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29750,⟨sg29746,⟨sg29744,⟨sg29743,⟨sg29742,True.intro,True.intro⟩,True.intro⟩,⟨sg29745,True.intro,True.intro⟩⟩,⟨sg29748,⟨sg29747,True.intro,True.intro⟩,⟨sg29749,True.intro,True.intro⟩⟩⟩,⟨sg29754,⟨sg29752,⟨sg29751,True.intro,True.intro⟩,⟨sg29753,True.intro,True.intro⟩⟩,⟨sg29756,⟨sg29755,True.intro,True.intro⟩,⟨sg29757,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_473All_oai := @OAI.UniversalTensorSquare.degreeTree43_473All_oai
