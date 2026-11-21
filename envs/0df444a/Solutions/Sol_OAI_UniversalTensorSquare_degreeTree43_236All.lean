-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_236All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:54:26.948562+00:00
-- url     : https://prove2.me/submissions/68364dd0-30eb-4c5e-8dd6-fbee4ee294db

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_234All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10300
import Theorems.Thm_OAI_UniversalTensorSquare_sg10302
import Theorems.Thm_OAI_UniversalTensorSquare_sg10303
import Theorems.Thm_OAI_UniversalTensorSquare_sg10304
import Theorems.Thm_OAI_UniversalTensorSquare_sg10305
import Theorems.Thm_OAI_UniversalTensorSquare_sg10306
import Theorems.Thm_OAI_UniversalTensorSquare_sg1379
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg236
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg26678
import Theorems.Thm_OAI_UniversalTensorSquare_sg26679
import Theorems.Thm_OAI_UniversalTensorSquare_sg26681
import Theorems.Thm_OAI_UniversalTensorSquare_sg26683
import Theorems.Thm_OAI_UniversalTensorSquare_sg26685
import Theorems.Thm_OAI_UniversalTensorSquare_sg26686
import Theorems.Thm_OAI_UniversalTensorSquare_sg26687
import Theorems.Thm_OAI_UniversalTensorSquare_sg26689
import Theorems.Thm_OAI_UniversalTensorSquare_sg26690
import Theorems.Thm_OAI_UniversalTensorSquare_sg26692
import Theorems.Thm_OAI_UniversalTensorSquare_sg26694
import Theorems.Thm_OAI_UniversalTensorSquare_sg26695
import Theorems.Thm_OAI_UniversalTensorSquare_sg26696
import Theorems.Thm_OAI_UniversalTensorSquare_sg26697
import Theorems.Thm_OAI_UniversalTensorSquare_sg26698
import Theorems.Thm_OAI_UniversalTensorSquare_sg26699
import Theorems.Thm_OAI_UniversalTensorSquare_sg26702
import Theorems.Thm_OAI_UniversalTensorSquare_sg26704
import Theorems.Thm_OAI_UniversalTensorSquare_sg26705
import Theorems.Thm_OAI_UniversalTensorSquare_sg26707
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg4930
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg596
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9831
import Theorems.Thm_OAI_UniversalTensorSquare_sg9832
import Theorems.Thm_OAI_UniversalTensorSquare_sg9841

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
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

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg594 : RowSquare [5,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg315

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

lemma sg738 : RowSquare [3,2,1,1,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg88

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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

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

lemma sg2253 : RowSquare [7,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg236

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

lemma sg3768 : RowSquare [3,3,2,2,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg390

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

lemma sg5565 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg590 sg594

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

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9189 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1379

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

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8819 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2253

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12621 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg4160

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

lemma sg14540 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg738 sg4930

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

lemma sg26677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10302

lemma sg26680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9831

lemma sg26682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10303

lemma sg26684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10300

lemma sg26688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9841

lemma sg26691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9832

lemma sg26693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10304

lemma sg26700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14540

lemma sg26701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5565 sg12621

lemma sg26703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10305

lemma sg26706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8819 sg9189

lemma sg26708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10306

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

lemma degreeTree43_235All : degreeTree43_235.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26693,⟨sg26685,⟨sg26681,⟨sg26679,⟨sg26678,True.intro,True.intro⟩,⟨sg26680,True.intro,True.intro⟩⟩,⟨sg26683,⟨sg26682,True.intro,True.intro⟩,⟨sg26684,True.intro,True.intro⟩⟩⟩,⟨sg26689,⟨sg26687,⟨sg26686,True.intro,True.intro⟩,⟨sg26688,True.intro,True.intro⟩⟩,⟨sg26691,⟨sg26690,True.intro,True.intro⟩,⟨sg26692,True.intro,True.intro⟩⟩⟩⟩,⟨sg26701,⟨sg26697,⟨sg26695,⟨sg26694,True.intro,True.intro⟩,⟨sg26696,True.intro,True.intro⟩⟩,⟨sg26699,⟨sg26698,True.intro,True.intro⟩,⟨sg26700,True.intro,True.intro⟩⟩⟩,⟨sg26705,⟨sg26703,⟨sg26702,True.intro,True.intro⟩,⟨sg26704,True.intro,True.intro⟩⟩,⟨sg26707,⟨sg26706,True.intro,True.intro⟩,⟨sg26708,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_236All_oai : degreeTree43_236.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26677,degreeTree43_234All,degreeTree43_235All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_236All_oai := @OAI.UniversalTensorSquare.degreeTree43_236All_oai
