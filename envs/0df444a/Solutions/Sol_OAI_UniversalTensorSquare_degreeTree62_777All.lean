-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_777All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:24:09.545504+00:00
-- url     : https://prove2.me/submissions/ecff57a4-964b-44e7-a770-259ec51b4b84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg18701
import Theorems.Thm_OAI_UniversalTensorSquare_sg18702
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg40581
import Theorems.Thm_OAI_UniversalTensorSquare_sg40582
import Theorems.Thm_OAI_UniversalTensorSquare_sg40583
import Theorems.Thm_OAI_UniversalTensorSquare_sg40584
import Theorems.Thm_OAI_UniversalTensorSquare_sg40585
import Theorems.Thm_OAI_UniversalTensorSquare_sg40586
import Theorems.Thm_OAI_UniversalTensorSquare_sg40587
import Theorems.Thm_OAI_UniversalTensorSquare_sg40588
import Theorems.Thm_OAI_UniversalTensorSquare_sg40589
import Theorems.Thm_OAI_UniversalTensorSquare_sg40590
import Theorems.Thm_OAI_UniversalTensorSquare_sg40591
import Theorems.Thm_OAI_UniversalTensorSquare_sg40592
import Theorems.Thm_OAI_UniversalTensorSquare_sg40594
import Theorems.Thm_OAI_UniversalTensorSquare_sg40595
import Theorems.Thm_OAI_UniversalTensorSquare_sg40596
import Theorems.Thm_OAI_UniversalTensorSquare_sg40597
import Theorems.Thm_OAI_UniversalTensorSquare_sg40598
import Theorems.Thm_OAI_UniversalTensorSquare_sg40599
import Theorems.Thm_OAI_UniversalTensorSquare_sg40600
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

lemma sgCert10 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 = -2 := by
  decide +kernel

lemma sg10 : RowSquare [2,1,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB10 sgT10 sgFlag10
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 ≠ 0
  rw [sgCert10]
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

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg396 : RowSquare [5,2,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg10

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

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

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

lemma sg5739 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg733

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

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

lemma sg20316 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5739

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 100. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40593 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,7,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18701

lemma sg40601 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,7,6,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18702

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

lemma degreeTree62_777All_oai : degreeTree62_777.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40591,⟨sg40586,⟨sg40583,⟨sg40582,⟨sg40581,True.intro,True.intro⟩,True.intro⟩,⟨sg40585,⟨sg40584,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40589,⟨sg40588,⟨sg40587,True.intro,True.intro⟩,True.intro⟩,⟨sg40590,True.intro,True.intro⟩⟩⟩,⟨sg40597,⟨sg40594,⟨sg40593,⟨sg40592,True.intro,True.intro⟩,True.intro⟩,⟨sg40596,⟨sg40595,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40600,⟨sg40599,⟨sg40598,True.intro,True.intro⟩,True.intro⟩,⟨sg40601,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_777All_oai := @OAI.UniversalTensorSquare.degreeTree62_777All_oai
