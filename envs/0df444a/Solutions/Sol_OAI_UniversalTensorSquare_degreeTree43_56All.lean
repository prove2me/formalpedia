-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_56All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:19:47.124892+00:00
-- url     : https://prove2.me/submissions/5b75c300-bc6f-4b97-b726-0eb77f423e45
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10227
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg24419
import Theorems.Thm_OAI_UniversalTensorSquare_sg24422
import Theorems.Thm_OAI_UniversalTensorSquare_sg24423
import Theorems.Thm_OAI_UniversalTensorSquare_sg24424
import Theorems.Thm_OAI_UniversalTensorSquare_sg24425
import Theorems.Thm_OAI_UniversalTensorSquare_sg24427
import Theorems.Thm_OAI_UniversalTensorSquare_sg24428
import Theorems.Thm_OAI_UniversalTensorSquare_sg24429
import Theorems.Thm_OAI_UniversalTensorSquare_sg24432
import Theorems.Thm_OAI_UniversalTensorSquare_sg24435
import Theorems.Thm_OAI_UniversalTensorSquare_sg24436
import Theorems.Thm_OAI_UniversalTensorSquare_sg24437
import Theorems.Thm_OAI_UniversalTensorSquare_sg24438
import Theorems.Thm_OAI_UniversalTensorSquare_sg24439
import Theorems.Thm_OAI_UniversalTensorSquare_sg24440
import Theorems.Thm_OAI_UniversalTensorSquare_sg24442
import Theorems.Thm_OAI_UniversalTensorSquare_sg24443
import Theorems.Thm_OAI_UniversalTensorSquare_sg24444
import Theorems.Thm_OAI_UniversalTensorSquare_sg24446
import Theorems.Thm_OAI_UniversalTensorSquare_sg24447
import Theorems.Thm_OAI_UniversalTensorSquare_sg24448
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert548

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

lemma sg548 : RowSquare [4,2,2,1] [2,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [8,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB548 sgT548 sgFlag548
  change solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 ≠ 0
  rw [sgCert548]
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

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg914 : RowSquare [5,2,1,1,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg52

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

lemma sg1037 : RowSquare [6,2,1,1] [3,2,2,2,1] := by
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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1375 : RowSquare [6,2,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg914

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

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

lemma sg1675 : RowSquare [5,2,2,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

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

lemma sg7794 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1757

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

lemma sg8449 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg548 sg1757

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

lemma sg10193 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1331

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

lemma sg10095 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1675

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

lemma sg8539 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1331

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8672 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1757

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

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

lemma sg9465 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1331

lemma sg9489 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1037 sg1757

lemma sg9660 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1331

lemma sg9723 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1757

lemma sg9724 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1375

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

lemma sg11243 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1757

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8732 sg9465

lemma sg24420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8539 sg10095

lemma sg24421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg7794 sg11243

lemma sg24426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9723

lemma sg24430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9724

lemma sg24431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9489

lemma sg24433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9465

lemma sg24434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8672 sg9660

lemma sg24441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10227

lemma sg24445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8449 sg10193

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

lemma degreeTree43_56All_oai : degreeTree43_56.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24433,⟨sg24425,⟨sg24421,⟨sg24419,⟨sg24418,True.intro,True.intro⟩,⟨sg24420,True.intro,True.intro⟩⟩,⟨sg24423,⟨sg24422,True.intro,True.intro⟩,⟨sg24424,True.intro,True.intro⟩⟩⟩,⟨sg24429,⟨sg24427,⟨sg24426,True.intro,True.intro⟩,⟨sg24428,True.intro,True.intro⟩⟩,⟨sg24431,⟨sg24430,True.intro,True.intro⟩,⟨sg24432,True.intro,True.intro⟩⟩⟩⟩,⟨sg24441,⟨sg24437,⟨sg24435,⟨sg24434,True.intro,True.intro⟩,⟨sg24436,True.intro,True.intro⟩⟩,⟨sg24439,⟨sg24438,True.intro,True.intro⟩,⟨sg24440,True.intro,True.intro⟩⟩⟩,⟨sg24445,⟨sg24443,⟨sg24442,True.intro,True.intro⟩,⟨sg24444,True.intro,True.intro⟩⟩,⟨sg24447,⟨sg24446,True.intro,True.intro⟩,⟨sg24448,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_56All_oai := @OAI.UniversalTensorSquare.degreeTree43_56All_oai
