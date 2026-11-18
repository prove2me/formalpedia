-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_103All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:13.392072+00:00
-- url     : https://prove2.me/submissions/33681435-d049-43fc-8607-441909eb89d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10244
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg24984
import Theorems.Thm_OAI_UniversalTensorSquare_sg24985
import Theorems.Thm_OAI_UniversalTensorSquare_sg24986
import Theorems.Thm_OAI_UniversalTensorSquare_sg24987
import Theorems.Thm_OAI_UniversalTensorSquare_sg24988
import Theorems.Thm_OAI_UniversalTensorSquare_sg24989
import Theorems.Thm_OAI_UniversalTensorSquare_sg24990
import Theorems.Thm_OAI_UniversalTensorSquare_sg24991
import Theorems.Thm_OAI_UniversalTensorSquare_sg24995
import Theorems.Thm_OAI_UniversalTensorSquare_sg24996
import Theorems.Thm_OAI_UniversalTensorSquare_sg24997
import Theorems.Thm_OAI_UniversalTensorSquare_sg24998
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg9518
import Theorems.Thm_OAI_UniversalTensorSquare_sg9752

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

lemma sg8720 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9752

lemma sg24993 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9518

lemma sg24994 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10244

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

lemma degreeTree43_103All_oai : degreeTree43_103.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24991,⟨sg24987,⟨sg24985,⟨sg24984,True.intro,True.intro⟩,⟨sg24986,True.intro,True.intro⟩⟩,⟨sg24989,⟨sg24988,True.intro,True.intro⟩,⟨sg24990,True.intro,True.intro⟩⟩⟩,⟨sg24995,⟨sg24993,⟨sg24992,True.intro,True.intro⟩,⟨sg24994,True.intro,True.intro⟩⟩,⟨sg24997,⟨sg24996,True.intro,True.intro⟩,⟨sg24998,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_103All_oai := @OAI.UniversalTensorSquare.degreeTree43_103All_oai
