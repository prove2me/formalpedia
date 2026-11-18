-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_929All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:28:14.693481+00:00
-- url     : https://prove2.me/submissions/e8ed6465-2db4-4e56-9366-52ac3a69df6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_927All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg42248
import Theorems.Thm_OAI_UniversalTensorSquare_sg42249
import Theorems.Thm_OAI_UniversalTensorSquare_sg42250
import Theorems.Thm_OAI_UniversalTensorSquare_sg42254
import Theorems.Thm_OAI_UniversalTensorSquare_sg42255
import Theorems.Thm_OAI_UniversalTensorSquare_sg42256
import Theorems.Thm_OAI_UniversalTensorSquare_sg42257
import Theorems.Thm_OAI_UniversalTensorSquare_sg42258
import Theorems.Thm_OAI_UniversalTensorSquare_sg42259
import Theorems.Thm_OAI_UniversalTensorSquare_sg42260
import Theorems.Thm_OAI_UniversalTensorSquare_sg42261
import Theorems.Thm_OAI_UniversalTensorSquare_sg42262
import Theorems.Thm_OAI_UniversalTensorSquare_sg42263
import Theorems.Thm_OAI_UniversalTensorSquare_sg42264
import Theorems.Thm_OAI_UniversalTensorSquare_sg42265
import Theorems.Thm_OAI_UniversalTensorSquare_sg42267
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg703
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sgCert165 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 = 15 := by
  decide +kernel

lemma sg165 : RowSquare [3,3,1] [2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [6,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB165 sgT165 sgFlag165
  change solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 ≠ 0
  rw [sgCert165]
  norm_num

lemma sgCert166 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 = 3 := by
  decide +kernel

lemma sg166 : RowSquare [3,3,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB166 sgT166 sgFlag166
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 ≠ 0
  rw [sgCert166]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert377 : solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 = -4 := by
  decide +kernel

lemma sg377 : RowSquare [5,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB377 sgT377 sgFlag377
  change solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 ≠ 0
  rw [sgCert377]
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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg30 : RowSquare [2,2,1] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg59 : RowSquare [2,2,1,1] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg130 : RowSquare [2,2,2,1] [5,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
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

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg236 : RowSquare [2,1,1,1,1,1,1] [6,2] := by
  exact rowSquare_join (by decide) sg17 sg20

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

lemma sg364 : RowSquare [4,4] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

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

lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg92

lemma sg1069 : RowSquare [6,3,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

lemma sg1109 : RowSquare [7,2,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg88

lemma sg1203 : RowSquare [4,3,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

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

lemma sg1904 : RowSquare [7,3,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg178

lemma sg1963 : RowSquare [8,2,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg17 sg373

lemma sg2006 : RowSquare [9,2,1] [6,4,1,1] := by
  exact rowSquare_join (by decide) sg88 sg105

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

lemma sg2110 : RowSquare [4,4,3,2] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg130

lemma sg2253 : RowSquare [7,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg236

lemma sg2391 : RowSquare [8,2,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg178

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

lemma sg2614 : RowSquare [5,4,3,2] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2110

lemma sg2856 : RowSquare [7,4,3] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg307

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

lemma sg3737 : RowSquare [9,4,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg1033

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

lemma sg4529 : RowSquare [10,2,2,2] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg377

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

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

lemma sg6548 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,1] := by
  exact rowSquare_join (by decide) sg1069 sg1109

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg748

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

lemma sg11683 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1963

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

lemma sg13639 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2856

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11748 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12486 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg3737

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

lemma sg11121 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2006

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

lemma sg14459 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg2626

lemma sg14461 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2253 sg2626

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

lemma sg15454 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4529

lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4167

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16077 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15454

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16570 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13639

lemma sg16636 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,4] := by
  exact rowSquare_join (by decide) sg52 sg12486

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18876 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,8,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg6548

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19504 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11683

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20125 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11121

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20314 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg5737

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20683 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14459

lemma sg20689 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14461

lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 104. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42247 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16570

lemma sg42251 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20125

lemma sg42252 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18876

lemma sg42253 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16077

lemma sg42266 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19504

lemma sg42268 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16636

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_928All : degreeTree62_928.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42258,⟨sg42253,⟨sg42250,⟨sg42249,⟨sg42248,True.intro,True.intro⟩,True.intro⟩,⟨sg42252,⟨sg42251,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42256,⟨sg42255,⟨sg42254,True.intro,True.intro⟩,True.intro⟩,⟨sg42257,True.intro,True.intro⟩⟩⟩,⟨sg42264,⟨sg42261,⟨sg42260,⟨sg42259,True.intro,True.intro⟩,True.intro⟩,⟨sg42263,⟨sg42262,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42267,⟨sg42266,⟨sg42265,True.intro,True.intro⟩,True.intro⟩,⟨sg42268,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_929All_oai : degreeTree62_929.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42247,degreeTree62_927All,degreeTree62_928All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_929All_oai := @OAI.UniversalTensorSquare.degreeTree62_929All_oai
