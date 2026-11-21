-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_16All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:37:16.114215+00:00
-- url     : https://prove2.me/submissions/0b8688de-1f0d-4121-bf91-3b3bfc9f9eba

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21933
import Theorems.Thm_OAI_UniversalTensorSquare_sg21934
import Theorems.Thm_OAI_UniversalTensorSquare_sg21935
import Theorems.Thm_OAI_UniversalTensorSquare_sg21936
import Theorems.Thm_OAI_UniversalTensorSquare_sg21938
import Theorems.Thm_OAI_UniversalTensorSquare_sg21940
import Theorems.Thm_OAI_UniversalTensorSquare_sg21941
import Theorems.Thm_OAI_UniversalTensorSquare_sg21942
import Theorems.Thm_OAI_UniversalTensorSquare_sg21943
import Theorems.Thm_OAI_UniversalTensorSquare_sg21944
import Theorems.Thm_OAI_UniversalTensorSquare_sg21946
import Theorems.Thm_OAI_UniversalTensorSquare_sg21947
import Theorems.Thm_OAI_UniversalTensorSquare_sg21948
import Theorems.Thm_OAI_UniversalTensorSquare_sg21949
import Theorems.Thm_OAI_UniversalTensorSquare_sg21952
import Theorems.Thm_OAI_UniversalTensorSquare_sg21955
import Theorems.Thm_OAI_UniversalTensorSquare_sg21956
import Theorems.Thm_OAI_UniversalTensorSquare_sg21957
import Theorems.Thm_OAI_UniversalTensorSquare_sg21958
import Theorems.Thm_OAI_UniversalTensorSquare_sg21959
import Theorems.Thm_OAI_UniversalTensorSquare_sg21960
import Theorems.Thm_OAI_UniversalTensorSquare_sg3912
import Theorems.Thm_OAI_UniversalTensorSquare_sg3913
import Theorems.Thm_OAI_UniversalTensorSquare_sg3914
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6676
import Theorems.Thm_OAI_UniversalTensorSquare_sg6677
import Theorems.Thm_OAI_UniversalTensorSquare_sg6771
import Theorems.Thm_OAI_UniversalTensorSquare_sg6775
import Theorems.Thm_OAI_UniversalTensorSquare_sg6777
import Theorems.Thm_OAI_UniversalTensorSquare_sg6778
import Theorems.Thm_OAI_UniversalTensorSquare_sg814

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6428 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg814

lemma sg6432 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3912

lemma sg6436 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3913

lemma sg6437 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3914

lemma sg6472 : RowSquare [7,5,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3964

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21937 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6778

lemma sg21939 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6436 sg6771

lemma sg21945 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6437 sg6771

lemma sg21950 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6676

lemma sg21951 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6432 sg6775

lemma sg21953 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6677

lemma sg21954 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg6432 sg6777

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_16All_oai : degreeTree39_16.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21947,⟨sg21940,⟨sg21936,⟨sg21934,⟨sg21933,True.intro,True.intro⟩,⟨sg21935,True.intro,True.intro⟩⟩,⟨sg21938,⟨sg21937,True.intro,True.intro⟩,⟨sg21939,True.intro,True.intro⟩⟩⟩,⟨sg21944,⟨sg21942,⟨sg21941,True.intro,True.intro⟩,⟨sg21943,True.intro,True.intro⟩⟩,⟨sg21946,⟨sg21945,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21954,⟨sg21951,⟨sg21949,⟨sg21948,True.intro,True.intro⟩,⟨sg21950,True.intro,True.intro⟩⟩,⟨sg21953,⟨sg21952,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21958,⟨sg21956,⟨sg21955,True.intro,True.intro⟩,⟨sg21957,True.intro,True.intro⟩⟩,⟨sg21960,⟨sg21959,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_16All_oai := @OAI.UniversalTensorSquare.degreeTree39_16All_oai
