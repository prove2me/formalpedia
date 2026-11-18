-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_522All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:10:03.683645+00:00
-- url     : https://prove2.me/submissions/1ff9639f-c865-49bc-8005-d05583124fa8
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg16165
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg37774
import Theorems.Thm_OAI_UniversalTensorSquare_sg37775
import Theorems.Thm_OAI_UniversalTensorSquare_sg37777
import Theorems.Thm_OAI_UniversalTensorSquare_sg37780
import Theorems.Thm_OAI_UniversalTensorSquare_sg37781
import Theorems.Thm_OAI_UniversalTensorSquare_sg37782
import Theorems.Thm_OAI_UniversalTensorSquare_sg37783
import Theorems.Thm_OAI_UniversalTensorSquare_sg37784
import Theorems.Thm_OAI_UniversalTensorSquare_sg37785
import Theorems.Thm_OAI_UniversalTensorSquare_sg37787
import Theorems.Thm_OAI_UniversalTensorSquare_sg37788
import Theorems.Thm_OAI_UniversalTensorSquare_sg37789
import Theorems.Thm_OAI_UniversalTensorSquare_sg37790
import Theorems.Thm_OAI_UniversalTensorSquare_sg37791
import Theorems.Thm_OAI_UniversalTensorSquare_sg37792
import Theorems.Thm_OAI_UniversalTensorSquare_sg37793
import Theorems.Thm_OAI_UniversalTensorSquare_sg37794
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg958

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

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg76 : RowSquare [3,2,1] [2,2,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1])) he) hh

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

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg63 : RowSquare [2,2,2] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg13

lemma sg147 : RowSquare [3,2,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg55

lemma sg161 : RowSquare [3,2,2] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg63

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg239 : RowSquare [2,2,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg16 sg16

lemma sg263 : RowSquare [3,1,1,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg33

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

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2370 : RowSquare [8,2,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2744 : RowSquare [7,3,2,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg586

lemma sg2879 : RowSquare [8,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4776 : RowSquare [5,4,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg910

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3335 : RowSquare [6,3,3,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg161 sg263

lemma sg3574 : RowSquare [8,3,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1756

lemma sg3616 : RowSquare [8,3,2,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4201 : RowSquare [7,3,3,1,1,1] [5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3335

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11748 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2251

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

lemma sg11177 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg958 sg2370

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14903 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2744 sg3616

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17410 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14903

lemma sg17487 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3574 sg4201

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18497 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg239 sg11177

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

lemma sg20502 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4776

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20804 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg147 sg11748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 93. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37776 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,5,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17487

lemma sg37778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20804 sg16165

lemma sg37779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,5,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18497

lemma sg37786 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,7,6,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17410

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_522All_oai : degreeTree62_522.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37784,⟨sg37779,⟨sg37776,⟨sg37775,⟨sg37774,True.intro,True.intro⟩,True.intro⟩,⟨sg37778,⟨sg37777,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37782,⟨sg37781,⟨sg37780,True.intro,True.intro⟩,True.intro⟩,⟨sg37783,True.intro,True.intro⟩⟩⟩,⟨sg37790,⟨sg37787,⟨sg37786,⟨sg37785,True.intro,True.intro⟩,True.intro⟩,⟨sg37789,⟨sg37788,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37793,⟨sg37792,⟨sg37791,True.intro,True.intro⟩,True.intro⟩,⟨sg37794,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_522All_oai := @OAI.UniversalTensorSquare.degreeTree62_522All_oai
