-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_57All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:17:57.78379+00:00
-- url     : https://prove2.me/submissions/668cac1f-ab59-4866-a7bf-01c330ed8053
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_56All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg10225
import Theorems.Thm_OAI_UniversalTensorSquare_sg10226
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg15004
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg24386
import Theorems.Thm_OAI_UniversalTensorSquare_sg24387
import Theorems.Thm_OAI_UniversalTensorSquare_sg24388
import Theorems.Thm_OAI_UniversalTensorSquare_sg24389
import Theorems.Thm_OAI_UniversalTensorSquare_sg24390
import Theorems.Thm_OAI_UniversalTensorSquare_sg24393
import Theorems.Thm_OAI_UniversalTensorSquare_sg24394
import Theorems.Thm_OAI_UniversalTensorSquare_sg24395
import Theorems.Thm_OAI_UniversalTensorSquare_sg24396
import Theorems.Thm_OAI_UniversalTensorSquare_sg24398
import Theorems.Thm_OAI_UniversalTensorSquare_sg24403
import Theorems.Thm_OAI_UniversalTensorSquare_sg24405
import Theorems.Thm_OAI_UniversalTensorSquare_sg24408
import Theorems.Thm_OAI_UniversalTensorSquare_sg24415
import Theorems.Thm_OAI_UniversalTensorSquare_sg24416
import Theorems.Thm_OAI_UniversalTensorSquare_sg24417
import Theorems.Thm_OAI_UniversalTensorSquare_sg26
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg312
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg481
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9195
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
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

lemma sg244 : RowSquare [2,2,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg17 sg18

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

lemma sg806 : RowSquare [4,1,1,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg2 sg383

lemma sg883 : RowSquare [4,4,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg481

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg1645 : RowSquare [4,3,2,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg178

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

lemma sg1777 : RowSquare [6,3,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg312

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

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

lemma sg2255 : RowSquare [7,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg806

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

lemma sg2632 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg92 sg244

lemma sg2694 : RowSquare [6,6,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg883

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

lemma sg5551 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1000

lemma sg5552 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg590 sg590

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

lemma sg6917 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1000

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

lemma sg8349 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1682

lemma sg8431 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg178 sg2632

lemma sg8505 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg33 sg3768

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

lemma sg9194 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1782

lemma sg9196 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1777

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

lemma sg10167 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1327

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

lemma sg10081 : RowSquare [6,5,3,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg2626

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

lemma sg8537 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1327

lemma sg8579 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1331

lemma sg8580 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6917

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10635 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg2255

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

lemma sg12618 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg4160

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

lemma sg14500 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg5735

lemma sg14501 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1645 sg3521

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

lemma sg24391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10226

lemma sg24392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg8431 sg10225

lemma sg24397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg8431 sg10226

lemma sg24399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14500

lemma sg24400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2694 sg15004

lemma sg24401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12618

lemma sg24402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14501

lemma sg24404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9194

lemma sg24406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8505 sg10167

lemma sg24407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12618

lemma sg24409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8579 sg10081

lemma sg24410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9195

lemma sg24411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8349 sg10635

lemma sg24412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8537 sg10095

lemma sg24413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8580 sg10081

lemma sg24414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9196

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

lemma degreeTree43_55All : degreeTree43_55.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24401,⟨sg24393,⟨sg24389,⟨sg24387,⟨sg24386,True.intro,True.intro⟩,⟨sg24388,True.intro,True.intro⟩⟩,⟨sg24391,⟨sg24390,True.intro,True.intro⟩,⟨sg24392,True.intro,True.intro⟩⟩⟩,⟨sg24397,⟨sg24395,⟨sg24394,True.intro,True.intro⟩,⟨sg24396,True.intro,True.intro⟩⟩,⟨sg24399,⟨sg24398,True.intro,True.intro⟩,⟨sg24400,True.intro,True.intro⟩⟩⟩⟩,⟨sg24409,⟨sg24405,⟨sg24403,⟨sg24402,True.intro,True.intro⟩,⟨sg24404,True.intro,True.intro⟩⟩,⟨sg24407,⟨sg24406,True.intro,True.intro⟩,⟨sg24408,True.intro,True.intro⟩⟩⟩,⟨sg24413,⟨sg24411,⟨sg24410,True.intro,True.intro⟩,⟨sg24412,True.intro,True.intro⟩⟩,⟨sg24415,⟨sg24414,True.intro,True.intro⟩,⟨sg24416,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_57All_oai : degreeTree43_57.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24417,degreeTree43_55All,degreeTree43_56All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_57All_oai := @OAI.UniversalTensorSquare.degreeTree43_57All_oai
