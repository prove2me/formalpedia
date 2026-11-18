-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_580All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:48:49.251683+00:00
-- url     : https://prove2.me/submissions/852e7228-6dc3-4682-b310-869669706028
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_576All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_579All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg10399
import Theorems.Thm_OAI_UniversalTensorSquare_sg10410
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg31050
import Theorems.Thm_OAI_UniversalTensorSquare_sg31054
import Theorems.Thm_OAI_UniversalTensorSquare_sg31056
import Theorems.Thm_OAI_UniversalTensorSquare_sg31058
import Theorems.Thm_OAI_UniversalTensorSquare_sg31059
import Theorems.Thm_OAI_UniversalTensorSquare_sg31060
import Theorems.Thm_OAI_UniversalTensorSquare_sg31061
import Theorems.Thm_OAI_UniversalTensorSquare_sg31062
import Theorems.Thm_OAI_UniversalTensorSquare_sg31063
import Theorems.Thm_OAI_UniversalTensorSquare_sg31064
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg4930
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9958
import Theorems.Thm_OAI_UniversalTensorSquare_sg9964
import Theorems.Thm_OAI_UniversalTensorSquare_sg9987

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

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

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

lemma sg747 : RowSquare [3,2,1,1,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg34 sg46

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

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

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

lemma sg8650 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg1327

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

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

lemma sg14544 : RowSquare [9,7,2,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg747 sg4930

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 76. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31049 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9987

lemma sg31051 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9964

lemma sg31052 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9964

lemma sg31053 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10399

lemma sg31055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9958

lemma sg31057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14544

lemma sg31065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10410

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

lemma degreeTree43_577All : degreeTree43_577.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31057,⟨sg31053,⟨sg31051,⟨sg31050,True.intro,True.intro⟩,⟨sg31052,True.intro,True.intro⟩⟩,⟨sg31055,⟨sg31054,True.intro,True.intro⟩,⟨sg31056,True.intro,True.intro⟩⟩⟩,⟨sg31061,⟨sg31059,⟨sg31058,True.intro,True.intro⟩,⟨sg31060,True.intro,True.intro⟩⟩,⟨sg31063,⟨sg31062,True.intro,True.intro⟩,⟨sg31064,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_578All : degreeTree43_578.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31049,degreeTree43_576All,degreeTree43_577All⟩

lemma degreeTree43_580All_oai : degreeTree43_580.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31065,degreeTree43_578All,degreeTree43_579All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_580All_oai := @OAI.UniversalTensorSquare.degreeTree43_580All_oai
