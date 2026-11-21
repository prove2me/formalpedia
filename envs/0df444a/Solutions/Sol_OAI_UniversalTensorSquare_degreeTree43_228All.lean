-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_228All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:29.086651+00:00
-- url     : https://prove2.me/submissions/20c0a157-2997-415b-a787-531912afc550

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10299
import Theorems.Thm_OAI_UniversalTensorSquare_sg10300
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg26581
import Theorems.Thm_OAI_UniversalTensorSquare_sg26582
import Theorems.Thm_OAI_UniversalTensorSquare_sg26583
import Theorems.Thm_OAI_UniversalTensorSquare_sg26584
import Theorems.Thm_OAI_UniversalTensorSquare_sg26585
import Theorems.Thm_OAI_UniversalTensorSquare_sg26588
import Theorems.Thm_OAI_UniversalTensorSquare_sg26592
import Theorems.Thm_OAI_UniversalTensorSquare_sg26593
import Theorems.Thm_OAI_UniversalTensorSquare_sg26594
import Theorems.Thm_OAI_UniversalTensorSquare_sg26595
import Theorems.Thm_OAI_UniversalTensorSquare_sg26597
import Theorems.Thm_OAI_UniversalTensorSquare_sg26598
import Theorems.Thm_OAI_UniversalTensorSquare_sg26599
import Theorems.Thm_OAI_UniversalTensorSquare_sg26601
import Theorems.Thm_OAI_UniversalTensorSquare_sg26602
import Theorems.Thm_OAI_UniversalTensorSquare_sg26604
import Theorems.Thm_OAI_UniversalTensorSquare_sg26606
import Theorems.Thm_OAI_UniversalTensorSquare_sg26607
import Theorems.Thm_OAI_UniversalTensorSquare_sg26608
import Theorems.Thm_OAI_UniversalTensorSquare_sg26609
import Theorems.Thm_OAI_UniversalTensorSquare_sg26610
import Theorems.Thm_OAI_UniversalTensorSquare_sg26611
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4622
import Theorems.Thm_OAI_UniversalTensorSquare_sg4832
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg525
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg960
import Theorems.Thm_OAI_UniversalTensorSquare_sg9865
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert297 : solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 = -5 := by
  decide +kernel

lemma sg297 : RowSquare [3,3,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB297 sgT297 sgFlag297
  change solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 ≠ 0
  rw [sgCert297]
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

lemma sg27 : RowSquare [2,2,1] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1482 : RowSquare [6,5] [4,4,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1934 : RowSquare [7,5] [5,4,3] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1437 : RowSquare [6,3,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg68

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

lemma sg2236 : RowSquare [6,5,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg297

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

lemma sg2870 : RowSquare [7,5,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg960

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

lemma sg3874 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg373

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

lemma sg8424 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg2626

lemma sg8524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1327

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

lemma sg10144 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg4622

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

lemma sg8732 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg1754

lemma sg8733 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg813 sg1327

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

lemma sg9508 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1437

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14510 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg5735

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

lemma sg14855 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1934 sg4832

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

lemma sg26586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10144

lemma sg26587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9865

lemma sg26589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15520

lemma sg26590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14510

lemma sg26591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14855

lemma sg26596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9508

lemma sg26600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10299

lemma sg26603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9508

lemma sg26605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10300

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

lemma degreeTree43_228All_oai : degreeTree43_228.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26596,⟨sg26588,⟨sg26584,⟨sg26582,⟨sg26581,True.intro,True.intro⟩,⟨sg26583,True.intro,True.intro⟩⟩,⟨sg26586,⟨sg26585,True.intro,True.intro⟩,⟨sg26587,True.intro,True.intro⟩⟩⟩,⟨sg26592,⟨sg26590,⟨sg26589,True.intro,True.intro⟩,⟨sg26591,True.intro,True.intro⟩⟩,⟨sg26594,⟨sg26593,True.intro,True.intro⟩,⟨sg26595,True.intro,True.intro⟩⟩⟩⟩,⟨sg26604,⟨sg26600,⟨sg26598,⟨sg26597,True.intro,True.intro⟩,⟨sg26599,True.intro,True.intro⟩⟩,⟨sg26602,⟨sg26601,True.intro,True.intro⟩,⟨sg26603,True.intro,True.intro⟩⟩⟩,⟨sg26608,⟨sg26606,⟨sg26605,True.intro,True.intro⟩,⟨sg26607,True.intro,True.intro⟩⟩,⟨sg26610,⟨sg26609,True.intro,True.intro⟩,⟨sg26611,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_228All_oai := @OAI.UniversalTensorSquare.degreeTree43_228All_oai
