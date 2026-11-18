-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_411All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:08.12569+00:00
-- url     : https://prove2.me/submissions/9a3dda06-1821-4441-9aed-7f79d92a2347
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg11469
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg181
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg262
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg28904
import Theorems.Thm_OAI_UniversalTensorSquare_sg28905
import Theorems.Thm_OAI_UniversalTensorSquare_sg28906
import Theorems.Thm_OAI_UniversalTensorSquare_sg28907
import Theorems.Thm_OAI_UniversalTensorSquare_sg28908
import Theorems.Thm_OAI_UniversalTensorSquare_sg28912
import Theorems.Thm_OAI_UniversalTensorSquare_sg28914
import Theorems.Thm_OAI_UniversalTensorSquare_sg28917
import Theorems.Thm_OAI_UniversalTensorSquare_sg28918
import Theorems.Thm_OAI_UniversalTensorSquare_sg28919
import Theorems.Thm_OAI_UniversalTensorSquare_sg28920
import Theorems.Thm_OAI_UniversalTensorSquare_sg28922
import Theorems.Thm_OAI_UniversalTensorSquare_sg28925
import Theorems.Thm_OAI_UniversalTensorSquare_sg28927
import Theorems.Thm_OAI_UniversalTensorSquare_sg28928
import Theorems.Thm_OAI_UniversalTensorSquare_sg28929
import Theorems.Thm_OAI_UniversalTensorSquare_sg28931
import Theorems.Thm_OAI_UniversalTensorSquare_sg28932
import Theorems.Thm_OAI_UniversalTensorSquare_sg28933
import Theorems.Thm_OAI_UniversalTensorSquare_sg28934
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4161
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg8444
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert563 : solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB563 sgT563) sgFlag563 = 9 := by
  decide +kernel

lemma sg563 : RowSquare [4,3,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB563 sgT563 sgFlag563
  change solveCompact 9 (.full [6,3]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [6,3] (Equiv.refl (Fin 9)) sgB563 sgT563) sgFlag563 ≠ 0
  rw [sgCert563]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1084 : RowSquare [6,4] [6,2,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1489 : RowSquare [6,5] [6,2,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
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

lemma sg134 : RowSquare [3,1,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg519 : RowSquare [4,1,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg523 : RowSquare [4,1,1,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg181

lemma sg528 : RowSquare [4,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg262

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

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

lemma sg1012 : RowSquare [6,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg315

lemma sg1026 : RowSquare [6,1,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg7 sg134

lemma sg1095 : RowSquare [7,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg373

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

lemma sg1352 : RowSquare [6,1,1,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg519

lemma sg1361 : RowSquare [6,1,1,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg523

lemma sg1402 : RowSquare [6,2,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg135

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

lemma sg1766 : RowSquare [6,2,1,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg262

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

lemma sg2184 : RowSquare [6,4,2,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg297

lemma sg2225 : RowSquare [6,5,1,1] [3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg563

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

lemma sg3869 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg373

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6925 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1005

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

lemma sg9009 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1095 sg1682

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6962 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1012

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

lemma sg10251 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1352

lemma sg10328 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1361

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

lemma sg9883 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1026 sg1754

lemma sg9884 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1402

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8877 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11342 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1766

lemma sg11475 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg4161

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

lemma sg14515 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg5735

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

lemma sg15539 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg6457

lemma sg15577 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg7812

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2184 sg15577

lemma sg28910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15539

lemma sg28911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14515

lemma sg28913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6962 sg11469

lemma sg28915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10328

lemma sg28916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8877 sg9009

lemma sg28921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6925 sg11475

lemma sg28923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10251

lemma sg28924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8652 sg9883

lemma sg28926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11342

lemma sg28930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9884

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

lemma degreeTree43_411All_oai : degreeTree43_411.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28919,⟨sg28911,⟨sg28907,⟨sg28905,⟨sg28904,True.intro,True.intro⟩,⟨sg28906,True.intro,True.intro⟩⟩,⟨sg28909,⟨sg28908,True.intro,True.intro⟩,⟨sg28910,True.intro,True.intro⟩⟩⟩,⟨sg28915,⟨sg28913,⟨sg28912,True.intro,True.intro⟩,⟨sg28914,True.intro,True.intro⟩⟩,⟨sg28917,⟨sg28916,True.intro,True.intro⟩,⟨sg28918,True.intro,True.intro⟩⟩⟩⟩,⟨sg28927,⟨sg28923,⟨sg28921,⟨sg28920,True.intro,True.intro⟩,⟨sg28922,True.intro,True.intro⟩⟩,⟨sg28925,⟨sg28924,True.intro,True.intro⟩,⟨sg28926,True.intro,True.intro⟩⟩⟩,⟨sg28931,⟨sg28929,⟨sg28928,True.intro,True.intro⟩,⟨sg28930,True.intro,True.intro⟩⟩,⟨sg28933,⟨sg28932,True.intro,True.intro⟩,⟨sg28934,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_411All_oai := @OAI.UniversalTensorSquare.degreeTree43_411All_oai
