-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_256All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:37:28.550515+00:00
-- url     : https://prove2.me/submissions/1be4f630-652e-4b6f-b8e9-69a49cc13e14
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20776
import Theorems.Thm_OAI_UniversalTensorSquare_sg20777
import Theorems.Thm_OAI_UniversalTensorSquare_sg20778
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg26936
import Theorems.Thm_OAI_UniversalTensorSquare_sg26937
import Theorems.Thm_OAI_UniversalTensorSquare_sg26939
import Theorems.Thm_OAI_UniversalTensorSquare_sg26940
import Theorems.Thm_OAI_UniversalTensorSquare_sg26942
import Theorems.Thm_OAI_UniversalTensorSquare_sg26943
import Theorems.Thm_OAI_UniversalTensorSquare_sg26944
import Theorems.Thm_OAI_UniversalTensorSquare_sg26946
import Theorems.Thm_OAI_UniversalTensorSquare_sg26947
import Theorems.Thm_OAI_UniversalTensorSquare_sg26949
import Theorems.Thm_OAI_UniversalTensorSquare_sg26950
import Theorems.Thm_OAI_UniversalTensorSquare_sg26952
import Theorems.Thm_OAI_UniversalTensorSquare_sg26953
import Theorems.Thm_OAI_UniversalTensorSquare_sg26954
import Theorems.Thm_OAI_UniversalTensorSquare_sg26955
import Theorems.Thm_OAI_UniversalTensorSquare_sg26956
import Theorems.Thm_OAI_UniversalTensorSquare_sg26957
import Theorems.Thm_OAI_UniversalTensorSquare_sg26958
import Theorems.Thm_OAI_UniversalTensorSquare_sg26959
import Theorems.Thm_OAI_UniversalTensorSquare_sg26960
import Theorems.Thm_OAI_UniversalTensorSquare_sg26961
import Theorems.Thm_OAI_UniversalTensorSquare_sg26962
import Theorems.Thm_OAI_UniversalTensorSquare_sg26963
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg9140
import Theorems.Thm_OAI_UniversalTensorSquare_sg9578
import Theorems.Thm_OAI_UniversalTensorSquare_sg9843

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

lemma sg26 : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg80 : RowSquare [3,2,1] [3,3] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,3])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,3]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,3]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3])) he) hh

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

lemma sg676 : RowSquare [6,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

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

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

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

lemma sg3875 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg373

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

lemma sg7810 : RowSquare [6,6,1,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg3875

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8776 : RowSquare [6,6,2,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg26 sg3875

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

lemma sg9443 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1417

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11238 : RowSquare [6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg2626

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21638 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20776

lemma sg21639 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20777

lemma sg21640 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20778

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

lemma sg26938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9140

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26941 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9843

lemma sg26945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9578

lemma sg26948 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,8,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7810 sg11238

lemma sg26951 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8776 sg9443

lemma sg26964 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21638

lemma sg26965 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21639

lemma sg26966 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg21640

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

lemma degreeTree43_256All_oai : degreeTree43_256.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26951,⟨sg26943,⟨sg26939,⟨sg26937,⟨sg26936,True.intro,True.intro⟩,⟨sg26938,True.intro,True.intro⟩⟩,⟨sg26941,⟨sg26940,True.intro,True.intro⟩,⟨sg26942,True.intro,True.intro⟩⟩⟩,⟨sg26947,⟨sg26945,⟨sg26944,True.intro,True.intro⟩,⟨sg26946,True.intro,True.intro⟩⟩,⟨sg26949,⟨sg26948,True.intro,True.intro⟩,⟨sg26950,True.intro,True.intro⟩⟩⟩⟩,⟨sg26959,⟨sg26955,⟨sg26953,⟨sg26952,True.intro,True.intro⟩,⟨sg26954,True.intro,True.intro⟩⟩,⟨sg26957,⟨sg26956,True.intro,True.intro⟩,⟨sg26958,True.intro,True.intro⟩⟩⟩,⟨sg26963,⟨sg26961,⟨sg26960,True.intro,True.intro⟩,⟨sg26962,True.intro,True.intro⟩⟩,⟨sg26965,⟨sg26964,True.intro,True.intro⟩,⟨sg26966,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_256All_oai := @OAI.UniversalTensorSquare.degreeTree43_256All_oai
