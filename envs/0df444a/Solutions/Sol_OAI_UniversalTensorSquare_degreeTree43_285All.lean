-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_285All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:37:36.855765+00:00
-- url     : https://prove2.me/submissions/2bcbb650-8788-49b7-9ff2-d1f150d8d927

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_283All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg105
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg1348
import Theorems.Thm_OAI_UniversalTensorSquare_sg1755
import Theorems.Thm_OAI_UniversalTensorSquare_sg18245
import Theorems.Thm_OAI_UniversalTensorSquare_sg27308
import Theorems.Thm_OAI_UniversalTensorSquare_sg27310
import Theorems.Thm_OAI_UniversalTensorSquare_sg27311
import Theorems.Thm_OAI_UniversalTensorSquare_sg27312
import Theorems.Thm_OAI_UniversalTensorSquare_sg27313
import Theorems.Thm_OAI_UniversalTensorSquare_sg27314
import Theorems.Thm_OAI_UniversalTensorSquare_sg27316
import Theorems.Thm_OAI_UniversalTensorSquare_sg27317
import Theorems.Thm_OAI_UniversalTensorSquare_sg27320
import Theorems.Thm_OAI_UniversalTensorSquare_sg27321
import Theorems.Thm_OAI_UniversalTensorSquare_sg295
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg55
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg814
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg9507
import Theorems.Thm_OAI_UniversalTensorSquare_sg9738

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert511 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 = 120 := by
  decide +kernel

lemma sg511 : RowSquare [3,3,2,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB511 sgT511 sgFlag511
  change solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 ≠ 0
  rw [sgCert511]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg77 : RowSquare [3,2,1] [2,2,2] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,2])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,2]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,2]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2])) he) hh

lemma sg1482 : RowSquare [6,5] [4,4,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1723 : RowSquare [5,4,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg77 sg55

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

lemma sg2238 : RowSquare [6,5,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg295

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

lemma sg2681 : RowSquare [6,5,2,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg511

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10309 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1348

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

lemma sg8658 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1755

lemma sg8736 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15014 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg5672

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15520 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg6457

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

lemma sg27306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9738

lemma sg27307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8430 sg10309

lemma sg27309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9507

lemma sg27315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18245

lemma sg27318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2238 sg15520

lemma sg27319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2681 sg15014

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

lemma degreeTree43_284All : degreeTree43_284.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27314,⟨sg27310,⟨sg27308,⟨sg27307,True.intro,True.intro⟩,⟨sg27309,True.intro,True.intro⟩⟩,⟨sg27312,⟨sg27311,True.intro,True.intro⟩,⟨sg27313,True.intro,True.intro⟩⟩⟩,⟨sg27318,⟨sg27316,⟨sg27315,True.intro,True.intro⟩,⟨sg27317,True.intro,True.intro⟩⟩,⟨sg27320,⟨sg27319,True.intro,True.intro⟩,⟨sg27321,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_285All_oai : degreeTree43_285.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27306,degreeTree43_283All,degreeTree43_284All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_285All_oai := @OAI.UniversalTensorSquare.degreeTree43_285All_oai
