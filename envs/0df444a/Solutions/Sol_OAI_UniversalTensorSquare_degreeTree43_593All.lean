-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_593All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:20:54.261628+00:00
-- url     : https://prove2.me/submissions/02f738a8-4239-4f89-ba24-c0ceb3545ced

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_592All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg1348
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg236
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg275
import Theorems.Thm_OAI_UniversalTensorSquare_sg31228
import Theorems.Thm_OAI_UniversalTensorSquare_sg31229
import Theorems.Thm_OAI_UniversalTensorSquare_sg31231
import Theorems.Thm_OAI_UniversalTensorSquare_sg31233
import Theorems.Thm_OAI_UniversalTensorSquare_sg31235
import Theorems.Thm_OAI_UniversalTensorSquare_sg31236
import Theorems.Thm_OAI_UniversalTensorSquare_sg31238
import Theorems.Thm_OAI_UniversalTensorSquare_sg31240
import Theorems.Thm_OAI_UniversalTensorSquare_sg31241
import Theorems.Thm_OAI_UniversalTensorSquare_sg31242
import Theorems.Thm_OAI_UniversalTensorSquare_sg31243
import Theorems.Thm_OAI_UniversalTensorSquare_sg31244
import Theorems.Thm_OAI_UniversalTensorSquare_sg31245
import Theorems.Thm_OAI_UniversalTensorSquare_sg31246
import Theorems.Thm_OAI_UniversalTensorSquare_sg31247
import Theorems.Thm_OAI_UniversalTensorSquare_sg31248
import Theorems.Thm_OAI_UniversalTensorSquare_sg31249
import Theorems.Thm_OAI_UniversalTensorSquare_sg31250
import Theorems.Thm_OAI_UniversalTensorSquare_sg31252
import Theorems.Thm_OAI_UniversalTensorSquare_sg31253
import Theorems.Thm_OAI_UniversalTensorSquare_sg31254
import Theorems.Thm_OAI_UniversalTensorSquare_sg31255
import Theorems.Thm_OAI_UniversalTensorSquare_sg31256
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg4832
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg562
import Theorems.Thm_OAI_UniversalTensorSquare_sg5757
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg588
import Theorems.Thm_OAI_UniversalTensorSquare_sg595
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg814
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert275

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

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1488 : RowSquare [6,5] [5,5,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1936 : RowSquare [7,5] [5,5,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
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

lemma sg116 : RowSquare [2,2,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg13

lemma sg694 : RowSquare [6,2,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

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

lemma sg741 : RowSquare [3,2,1,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

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

lemma sg1244 : RowSquare [5,1,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1001

lemma sg1435 : RowSquare [6,3,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg143

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

lemma sg1695 : RowSquare [5,3,2,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg116

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

lemma sg2241 : RowSquare [6,5,1,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg40 sg297

lemma sg2253 : RowSquare [7,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg236

lemma sg2269 : RowSquare [7,1,1,1,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1244

lemma sg2305 : RowSquare [7,3,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg535

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

lemma sg2876 : RowSquare [7,5,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg562

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3169 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg694

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

lemma sg5585 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg595 sg595

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

lemma sg8401 : RowSquare [5,5,3,2,1,1,1,1,1,1] [6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1695

lemma sg8414 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2626

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

lemma sg9199 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2305

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

lemma sg10499 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg1348 sg1348

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

lemma sg8736 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1327

lemma sg8843 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg2253

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

lemma sg10602 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2251

lemma sg10832 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg595 sg2269

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

lemma sg12620 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg4160

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

lemma sg9583 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1435

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

lemma sg14806 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg741 sg5757

lemma sg14857 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1936 sg4832

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

lemma sg15536 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg6457

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

lemma sg31227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8843 sg9199

lemma sg31230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5585 sg12620

lemma sg31232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10499

lemma sg31234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10832

lemma sg31237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8401 sg10602

lemma sg31239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9583

lemma sg31251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2876 sg14857

lemma sg31257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15536

lemma sg31258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3169 sg14806

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

lemma degreeTree43_591All : degreeTree43_591.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31242,⟨sg31234,⟨sg31230,⟨sg31228,⟨sg31227,True.intro,True.intro⟩,⟨sg31229,True.intro,True.intro⟩⟩,⟨sg31232,⟨sg31231,True.intro,True.intro⟩,⟨sg31233,True.intro,True.intro⟩⟩⟩,⟨sg31238,⟨sg31236,⟨sg31235,True.intro,True.intro⟩,⟨sg31237,True.intro,True.intro⟩⟩,⟨sg31240,⟨sg31239,True.intro,True.intro⟩,⟨sg31241,True.intro,True.intro⟩⟩⟩⟩,⟨sg31250,⟨sg31246,⟨sg31244,⟨sg31243,True.intro,True.intro⟩,⟨sg31245,True.intro,True.intro⟩⟩,⟨sg31248,⟨sg31247,True.intro,True.intro⟩,⟨sg31249,True.intro,True.intro⟩⟩⟩,⟨sg31254,⟨sg31252,⟨sg31251,True.intro,True.intro⟩,⟨sg31253,True.intro,True.intro⟩⟩,⟨sg31256,⟨sg31255,True.intro,True.intro⟩,⟨sg31257,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_593All_oai : degreeTree43_593.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31258,degreeTree43_591All,degreeTree43_592All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_593All_oai := @OAI.UniversalTensorSquare.degreeTree43_593All_oai
