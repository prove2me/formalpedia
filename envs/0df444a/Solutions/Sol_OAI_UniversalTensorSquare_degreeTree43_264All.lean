-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_264All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:37.791197+00:00
-- url     : https://prove2.me/submissions/9d307b2a-f8c7-4179-b3b5-c77b53a51a5b
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1023
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg27049
import Theorems.Thm_OAI_UniversalTensorSquare_sg27051
import Theorems.Thm_OAI_UniversalTensorSquare_sg27052
import Theorems.Thm_OAI_UniversalTensorSquare_sg27053
import Theorems.Thm_OAI_UniversalTensorSquare_sg27057
import Theorems.Thm_OAI_UniversalTensorSquare_sg27058
import Theorems.Thm_OAI_UniversalTensorSquare_sg27059
import Theorems.Thm_OAI_UniversalTensorSquare_sg27061
import Theorems.Thm_OAI_UniversalTensorSquare_sg27062
import Theorems.Thm_OAI_UniversalTensorSquare_sg27063
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg5236
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sgCert71 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 = 2 := by
  decide +kernel

lemma sg71 : RowSquare [3,1,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB71 sgT71 sgFlag71
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 ≠ 0
  rw [sgCert71]
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

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg602 : RowSquare [5,1,1,1,1] [4,4,1] := by
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

lemma sg825 : RowSquare [4,2,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg71

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

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

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

lemma sg5537 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg313 sg998

lemma sg5538 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg588

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

lemma sg9844 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1754

lemma sg10105 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg2626

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

lemma sg8546 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1330

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

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

lemma sg12630 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg4160

lemma sg12695 : RowSquare [8,6,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg825 sg3521

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5537 sg12630

lemma sg27054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8651 sg9844

lemma sg27055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5538 sg12630

lemma sg27056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5236 sg12695

lemma sg27060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8546 sg10105

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

lemma degreeTree43_264All_oai : degreeTree43_264.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27056,⟨sg27052,⟨sg27050,⟨sg27049,True.intro,True.intro⟩,⟨sg27051,True.intro,True.intro⟩⟩,⟨sg27054,⟨sg27053,True.intro,True.intro⟩,⟨sg27055,True.intro,True.intro⟩⟩⟩,⟨sg27060,⟨sg27058,⟨sg27057,True.intro,True.intro⟩,⟨sg27059,True.intro,True.intro⟩⟩,⟨sg27062,⟨sg27061,True.intro,True.intro⟩,⟨sg27063,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_264All_oai := @OAI.UniversalTensorSquare.degreeTree43_264All_oai
