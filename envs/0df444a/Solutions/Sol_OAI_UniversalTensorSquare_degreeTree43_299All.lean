-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_299All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:42.359899+00:00
-- url     : https://prove2.me/submissions/0b8531ee-f3cf-4b0a-a44f-55bba85d9665
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_298All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10315
import Theorems.Thm_OAI_UniversalTensorSquare_sg10316
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg27484
import Theorems.Thm_OAI_UniversalTensorSquare_sg27485
import Theorems.Thm_OAI_UniversalTensorSquare_sg27486
import Theorems.Thm_OAI_UniversalTensorSquare_sg27488
import Theorems.Thm_OAI_UniversalTensorSquare_sg27490
import Theorems.Thm_OAI_UniversalTensorSquare_sg27491
import Theorems.Thm_OAI_UniversalTensorSquare_sg27493
import Theorems.Thm_OAI_UniversalTensorSquare_sg27498
import Theorems.Thm_OAI_UniversalTensorSquare_sg27499
import Theorems.Thm_OAI_UniversalTensorSquare_sg27500
import Theorems.Thm_OAI_UniversalTensorSquare_sg27501
import Theorems.Thm_OAI_UniversalTensorSquare_sg27503
import Theorems.Thm_OAI_UniversalTensorSquare_sg27504
import Theorems.Thm_OAI_UniversalTensorSquare_sg27505
import Theorems.Thm_OAI_UniversalTensorSquare_sg27506
import Theorems.Thm_OAI_UniversalTensorSquare_sg27507
import Theorems.Thm_OAI_UniversalTensorSquare_sg27509
import Theorems.Thm_OAI_UniversalTensorSquare_sg27510
import Theorems.Thm_OAI_UniversalTensorSquare_sg27511
import Theorems.Thm_OAI_UniversalTensorSquare_sg27513
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg378
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg9590
import Theorems.Thm_OAI_UniversalTensorSquare_sg9738
import Theorems.Thm_OAI_UniversalTensorSquare_sg9753
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sgCert194 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 = 17 := by
  decide +kernel

lemma sg194 : RowSquare [4,2,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB194 sgT194 sgFlag194
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 ≠ 0
  rw [sgCert194]
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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg134 : RowSquare [3,1,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

lemma sg595 : RowSquare [5,1,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg134

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

lemma sg1061 : RowSquare [6,2,2] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

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

lemma sg1339 : RowSquare [6,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg525

lemma sg1348 : RowSquare [6,1,1,1,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg520

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1766 : RowSquare [6,2,1,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg262

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

lemma sg4571 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg194 sg1061

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

lemma sg8396 : RowSquare [5,5,3,2,1,1,1,1,1,1] [5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg4571

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

lemma sg10314 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1348

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

lemma sg9754 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1766

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

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

lemma sg9588 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1348

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

lemma sg27487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9588

lemma sg27489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10314

lemma sg27492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8396 sg10602

lemma sg27494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9588

lemma sg27495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9738

lemma sg27496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9590

lemma sg27497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10315

lemma sg27502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10315

lemma sg27508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10316

lemma sg27512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9753

lemma sg27514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10317

lemma sg27515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9754

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

lemma degreeTree43_297All : degreeTree43_297.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27499,⟨sg27491,⟨sg27487,⟨sg27485,⟨sg27484,True.intro,True.intro⟩,⟨sg27486,True.intro,True.intro⟩⟩,⟨sg27489,⟨sg27488,True.intro,True.intro⟩,⟨sg27490,True.intro,True.intro⟩⟩⟩,⟨sg27495,⟨sg27493,⟨sg27492,True.intro,True.intro⟩,⟨sg27494,True.intro,True.intro⟩⟩,⟨sg27497,⟨sg27496,True.intro,True.intro⟩,⟨sg27498,True.intro,True.intro⟩⟩⟩⟩,⟨sg27507,⟨sg27503,⟨sg27501,⟨sg27500,True.intro,True.intro⟩,⟨sg27502,True.intro,True.intro⟩⟩,⟨sg27505,⟨sg27504,True.intro,True.intro⟩,⟨sg27506,True.intro,True.intro⟩⟩⟩,⟨sg27511,⟨sg27509,⟨sg27508,True.intro,True.intro⟩,⟨sg27510,True.intro,True.intro⟩⟩,⟨sg27513,⟨sg27512,True.intro,True.intro⟩,⟨sg27514,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_299All_oai : degreeTree43_299.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27515,degreeTree43_297All,degreeTree43_298All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_299All_oai := @OAI.UniversalTensorSquare.degreeTree43_299All_oai
