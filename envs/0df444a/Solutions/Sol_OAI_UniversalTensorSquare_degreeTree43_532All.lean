-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_532All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:54.65888+00:00
-- url     : https://prove2.me/submissions/361f47b8-23ef-425b-af40-74933c12e5dd
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg30459
import Theorems.Thm_OAI_UniversalTensorSquare_sg30460
import Theorems.Thm_OAI_UniversalTensorSquare_sg30463
import Theorems.Thm_OAI_UniversalTensorSquare_sg30464
import Theorems.Thm_OAI_UniversalTensorSquare_sg30465
import Theorems.Thm_OAI_UniversalTensorSquare_sg30467
import Theorems.Thm_OAI_UniversalTensorSquare_sg30468
import Theorems.Thm_OAI_UniversalTensorSquare_sg30469
import Theorems.Thm_OAI_UniversalTensorSquare_sg30470
import Theorems.Thm_OAI_UniversalTensorSquare_sg30471
import Theorems.Thm_OAI_UniversalTensorSquare_sg30472
import Theorems.Thm_OAI_UniversalTensorSquare_sg30473
import Theorems.Thm_OAI_UniversalTensorSquare_sg30474
import Theorems.Thm_OAI_UniversalTensorSquare_sg30475
import Theorems.Thm_OAI_UniversalTensorSquare_sg30476
import Theorems.Thm_OAI_UniversalTensorSquare_sg30477
import Theorems.Thm_OAI_UniversalTensorSquare_sg30478
import Theorems.Thm_OAI_UniversalTensorSquare_sg30479
import Theorems.Thm_OAI_UniversalTensorSquare_sg30480
import Theorems.Thm_OAI_UniversalTensorSquare_sg30481
import Theorems.Thm_OAI_UniversalTensorSquare_sg30482
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg378
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg5261
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780
import Theorems.Thm_OAI_UniversalTensorSquare_sg9281
import Theorems.Thm_OAI_UniversalTensorSquare_sg9282
import Theorems.Thm_OAI_UniversalTensorSquare_sg9618
import Theorems.Thm_OAI_UniversalTensorSquare_sg9619

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

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg123 : RowSquare [2,2,2,1] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1081 : RowSquare [6,4] [5,3,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg270 : RowSquare [3,2,1,1,1] [2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg32

lemma sg273 : RowSquare [3,2,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg32

lemma sg276 : RowSquare [3,2,1,1,1] [3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg34

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

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

lemma sg1286 : RowSquare [5,3,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg276

lemma sg1498 : RowSquare [7,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg586

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

lemma sg1831 : RowSquare [6,4,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg97 sg55

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

lemma sg2199 : RowSquare [6,4,2,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg97 sg123

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

lemma sg8791 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg2251

lemma sg8800 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg2251

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

lemma sg12690 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg4345

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

lemma sg9351 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1286

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

lemma sg15569 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1081 sg7812

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17121 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1081 sg8780

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 74. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9281

lemma sg30454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9618

lemma sg30455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9282

lemma sg30456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9282

lemma sg30457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9282

lemma sg30458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9619

lemma sg30461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17121

lemma sg30462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15569

lemma sg30466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5261 sg12690

lemma sg30483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9351

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

lemma degreeTree43_532All_oai : degreeTree43_532.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30468,⟨sg30460,⟨sg30456,⟨sg30454,⟨sg30453,True.intro,True.intro⟩,⟨sg30455,True.intro,True.intro⟩⟩,⟨sg30458,⟨sg30457,True.intro,True.intro⟩,⟨sg30459,True.intro,True.intro⟩⟩⟩,⟨sg30464,⟨sg30462,⟨sg30461,True.intro,True.intro⟩,⟨sg30463,True.intro,True.intro⟩⟩,⟨sg30466,⟨sg30465,True.intro,True.intro⟩,⟨sg30467,True.intro,True.intro⟩⟩⟩⟩,⟨sg30476,⟨sg30472,⟨sg30470,⟨sg30469,True.intro,True.intro⟩,⟨sg30471,True.intro,True.intro⟩⟩,⟨sg30474,⟨sg30473,True.intro,True.intro⟩,⟨sg30475,True.intro,True.intro⟩⟩⟩,⟨sg30480,⟨sg30478,⟨sg30477,True.intro,True.intro⟩,⟨sg30479,True.intro,True.intro⟩⟩,⟨sg30482,⟨sg30481,True.intro,True.intro⟩,⟨sg30483,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_532All_oai := @OAI.UniversalTensorSquare.degreeTree43_532All_oai
