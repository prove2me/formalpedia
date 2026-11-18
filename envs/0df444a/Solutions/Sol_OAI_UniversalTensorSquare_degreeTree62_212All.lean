-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_212All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:03:46.080324+00:00
-- url     : https://prove2.me/submissions/5b3ce434-3bcb-448d-8c28-c6b40adfe177
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515
import Theorems.Thm_OAI_UniversalTensorSquare_sg20516
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2373
import Theorems.Thm_OAI_UniversalTensorSquare_sg2746
import Theorems.Thm_OAI_UniversalTensorSquare_sg2806
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg314
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34376
import Theorems.Thm_OAI_UniversalTensorSquare_sg34378
import Theorems.Thm_OAI_UniversalTensorSquare_sg34380
import Theorems.Thm_OAI_UniversalTensorSquare_sg34382
import Theorems.Thm_OAI_UniversalTensorSquare_sg34383
import Theorems.Thm_OAI_UniversalTensorSquare_sg34384
import Theorems.Thm_OAI_UniversalTensorSquare_sg34385
import Theorems.Thm_OAI_UniversalTensorSquare_sg34386
import Theorems.Thm_OAI_UniversalTensorSquare_sg34389
import Theorems.Thm_OAI_UniversalTensorSquare_sg34391
import Theorems.Thm_OAI_UniversalTensorSquare_sg34392
import Theorems.Thm_OAI_UniversalTensorSquare_sg34393
import Theorems.Thm_OAI_UniversalTensorSquare_sg34394
import Theorems.Thm_OAI_UniversalTensorSquare_sg34395
import Theorems.Thm_OAI_UniversalTensorSquare_sg34396
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg4303
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
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

lemma sg137 : RowSquare [3,1,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg254 : RowSquare [2,2,2,2] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg137

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

lemma sg733 : RowSquare [3,1,1,1,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg20 sg92

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

lemma sg2293 : RowSquare [7,3,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg588

lemma sg2392 : RowSquare [8,2,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg371

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

lemma sg2907 : RowSquare [8,2,2,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg589

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

lemma sg3726 : RowSquare [9,3,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1033

lemma sg3967 : RowSquare [5,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg588

lemma sg4044 : RowSquare [6,3,3,3,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg314 sg254

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3501 : RowSquare [7,4,3,1] [2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg306

lemma sg3524 : RowSquare [8,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg733

lemma sg3565 : RowSquare [8,2,2,2,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg315

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

lemma sg13737 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2392 sg2806

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

lemma sg14240 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2907

lemma sg14241 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg2373 sg2746

lemma sg14319 : RowSquare [6,4,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg3501

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

lemma sg15796 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg3726 sg4044

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

lemma sg16684 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg3565 sg4303

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19216 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14240

lemma sg19217 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14241

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

lemma sg19620 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14319

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

lemma sg20646 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3967

lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11748

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

lemma sg17315 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13737

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34377 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17315

lemma sg34379 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17315

lemma sg34381 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19216

lemma sg34387 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19217

lemma sg34388 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20646 sg16684

lemma sg34390 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,7,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15796

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

lemma degreeTree62_212All_oai : degreeTree62_212.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34386,⟨sg34381,⟨sg34378,⟨sg34377,⟨sg34376,True.intro,True.intro⟩,True.intro⟩,⟨sg34380,⟨sg34379,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34384,⟨sg34383,⟨sg34382,True.intro,True.intro⟩,True.intro⟩,⟨sg34385,True.intro,True.intro⟩⟩⟩,⟨sg34392,⟨sg34389,⟨sg34388,⟨sg34387,True.intro,True.intro⟩,True.intro⟩,⟨sg34391,⟨sg34390,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34395,⟨sg34394,⟨sg34393,True.intro,True.intro⟩,True.intro⟩,⟨sg34396,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_212All_oai := @OAI.UniversalTensorSquare.degreeTree62_212All_oai
