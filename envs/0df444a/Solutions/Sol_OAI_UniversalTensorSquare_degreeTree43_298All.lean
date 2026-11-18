-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_298All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:42.958141+00:00
-- url     : https://prove2.me/submissions/6841775d-1bbb-4700-b14f-30ddb4890237
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg1008
import Theorems.Thm_OAI_UniversalTensorSquare_sg10318
import Theorems.Thm_OAI_UniversalTensorSquare_sg10319
import Theorems.Thm_OAI_UniversalTensorSquare_sg1262
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1378
import Theorems.Thm_OAI_UniversalTensorSquare_sg1379
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg27516
import Theorems.Thm_OAI_UniversalTensorSquare_sg27517
import Theorems.Thm_OAI_UniversalTensorSquare_sg27524
import Theorems.Thm_OAI_UniversalTensorSquare_sg27526
import Theorems.Thm_OAI_UniversalTensorSquare_sg27528
import Theorems.Thm_OAI_UniversalTensorSquare_sg27530
import Theorems.Thm_OAI_UniversalTensorSquare_sg27532
import Theorems.Thm_OAI_UniversalTensorSquare_sg27535
import Theorems.Thm_OAI_UniversalTensorSquare_sg27538
import Theorems.Thm_OAI_UniversalTensorSquare_sg27539
import Theorems.Thm_OAI_UniversalTensorSquare_sg27541
import Theorems.Thm_OAI_UniversalTensorSquare_sg27542
import Theorems.Thm_OAI_UniversalTensorSquare_sg27543
import Theorems.Thm_OAI_UniversalTensorSquare_sg27544
import Theorems.Thm_OAI_UniversalTensorSquare_sg27545
import Theorems.Thm_OAI_UniversalTensorSquare_sg27546
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg378
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9738
import Theorems.Thm_OAI_UniversalTensorSquare_sg9756
import Theorems.Thm_OAI_UniversalTensorSquare_sg9761

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

lemma sgCert67 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 = -8 := by
  decide +kernel

lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB67 sgT67 sgFlag67
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 ≠ 0
  rw [sgCert67]
  norm_num

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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

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

lemma sg1329 : RowSquare [6,1,1,1,1,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg111

lemma sg1339 : RowSquare [6,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg525

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

lemma sg1765 : RowSquare [6,2,1,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg262

lemma sg1899 : RowSquare [7,2,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg67

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

lemma sg4745 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg586

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

lemma sg9045 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1899

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

lemma sg10317 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1339 sg1339

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9741 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1378

lemma sg9744 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1379

lemma sg9749 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1757

lemma sg9751 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1765

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

lemma sg8663 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1755

lemma sg8668 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1262

lemma sg8870 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4745

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 67. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10318

lemma sg27519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9741

lemma sg27520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10319

lemma sg27521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9756

lemma sg27522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10317

lemma sg27523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9738

lemma sg27525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10317

lemma sg27527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9744

lemma sg27529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10318

lemma sg27531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10319

lemma sg27533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9761

lemma sg27534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10319

lemma sg27536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8870 sg9045

lemma sg27537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9749

lemma sg27540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9751

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

lemma degreeTree43_298All_oai : degreeTree43_298.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27531,⟨sg27523,⟨sg27519,⟨sg27517,⟨sg27516,True.intro,True.intro⟩,⟨sg27518,True.intro,True.intro⟩⟩,⟨sg27521,⟨sg27520,True.intro,True.intro⟩,⟨sg27522,True.intro,True.intro⟩⟩⟩,⟨sg27527,⟨sg27525,⟨sg27524,True.intro,True.intro⟩,⟨sg27526,True.intro,True.intro⟩⟩,⟨sg27529,⟨sg27528,True.intro,True.intro⟩,⟨sg27530,True.intro,True.intro⟩⟩⟩⟩,⟨sg27539,⟨sg27535,⟨sg27533,⟨sg27532,True.intro,True.intro⟩,⟨sg27534,True.intro,True.intro⟩⟩,⟨sg27537,⟨sg27536,True.intro,True.intro⟩,⟨sg27538,True.intro,True.intro⟩⟩⟩,⟨sg27543,⟨sg27541,⟨sg27540,True.intro,True.intro⟩,⟨sg27542,True.intro,True.intro⟩⟩,⟨sg27545,⟨sg27544,True.intro,True.intro⟩,⟨sg27546,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_298All_oai := @OAI.UniversalTensorSquare.degreeTree43_298All_oai
