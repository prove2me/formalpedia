-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_421All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:12.179681+00:00
-- url     : https://prove2.me/submissions/ab775216-b857-4f64-a4c3-116a003eee5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg29066
import Theorems.Thm_OAI_UniversalTensorSquare_sg29072
import Theorems.Thm_OAI_UniversalTensorSquare_sg29073
import Theorems.Thm_OAI_UniversalTensorSquare_sg29074
import Theorems.Thm_OAI_UniversalTensorSquare_sg29078
import Theorems.Thm_OAI_UniversalTensorSquare_sg29079
import Theorems.Thm_OAI_UniversalTensorSquare_sg29081
import Theorems.Thm_OAI_UniversalTensorSquare_sg29082
import Theorems.Thm_OAI_UniversalTensorSquare_sg29083
import Theorems.Thm_OAI_UniversalTensorSquare_sg29084
import Theorems.Thm_OAI_UniversalTensorSquare_sg29086
import Theorems.Thm_OAI_UniversalTensorSquare_sg29088
import Theorems.Thm_OAI_UniversalTensorSquare_sg29089
import Theorems.Thm_OAI_UniversalTensorSquare_sg29090
import Theorems.Thm_OAI_UniversalTensorSquare_sg29093
import Theorems.Thm_OAI_UniversalTensorSquare_sg29094
import Theorems.Thm_OAI_UniversalTensorSquare_sg29095
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg4161
import Theorems.Thm_OAI_UniversalTensorSquare_sg4930
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg637
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg9035
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9256
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

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
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

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg260 : RowSquare [3,1,1,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg416 : RowSquare [6,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg33

lemma sg447 : RowSquare [3,1,1,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg32

lemma sg594 : RowSquare [5,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg315

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg693 : RowSquare [6,2,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg390

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

lemma sg708 : RowSquare [7,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg32

lemma sg813 : RowSquare [4,2,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1393 : RowSquare [6,2,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg271

lemma sg1441 : RowSquare [6,3,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg69

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

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5055 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg693

lemma sg5320 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg416 sg1000

lemma sg5321 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg590 sg708

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

lemma sg4575 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg390 sg637

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

lemma sg5581 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3869

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

lemma sg6746 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1095

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

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

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

lemma sg9327 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1393

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

lemma sg6941 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1005

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

lemma sg9888 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6746

lemma sg9917 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5055

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8732 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg1754

lemma sg8733 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg813 sg1327

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

lemma sg8827 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg2702

lemma sg8871 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg260 sg2251

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

lemma sg10777 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5320

lemma sg10778 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5321

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

lemma sg11471 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg4160

lemma sg11477 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg4161

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13499 : RowSquare [9,7,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg447 sg4930

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

lemma sg9537 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1441

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5581 sg12618

lemma sg29067 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8827 sg9194

lemma sg29068 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9327

lemma sg29069 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9537

lemma sg29070 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4575 sg13499

lemma sg29071 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11471

lemma sg29075 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9888

lemma sg29076 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9537

lemma sg29077 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11477

lemma sg29080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10777

lemma sg29085 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9917

lemma sg29087 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9256

lemma sg29091 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8871 sg9035

lemma sg29092 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,6,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10778

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

lemma degreeTree43_421All_oai : degreeTree43_421.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29080,⟨sg29072,⟨sg29068,⟨sg29066,⟨sg29065,True.intro,True.intro⟩,⟨sg29067,True.intro,True.intro⟩⟩,⟨sg29070,⟨sg29069,True.intro,True.intro⟩,⟨sg29071,True.intro,True.intro⟩⟩⟩,⟨sg29076,⟨sg29074,⟨sg29073,True.intro,True.intro⟩,⟨sg29075,True.intro,True.intro⟩⟩,⟨sg29078,⟨sg29077,True.intro,True.intro⟩,⟨sg29079,True.intro,True.intro⟩⟩⟩⟩,⟨sg29088,⟨sg29084,⟨sg29082,⟨sg29081,True.intro,True.intro⟩,⟨sg29083,True.intro,True.intro⟩⟩,⟨sg29086,⟨sg29085,True.intro,True.intro⟩,⟨sg29087,True.intro,True.intro⟩⟩⟩,⟨sg29092,⟨sg29090,⟨sg29089,True.intro,True.intro⟩,⟨sg29091,True.intro,True.intro⟩⟩,⟨sg29094,⟨sg29093,True.intro,True.intro⟩,⟨sg29095,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_421All_oai := @OAI.UniversalTensorSquare.degreeTree43_421All_oai
