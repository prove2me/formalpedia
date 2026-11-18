-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_94All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:28:27.810973+00:00
-- url     : https://prove2.me/submissions/7f7d99f5-b47e-4d23-af26-531dba7904a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg20531
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33060
import Theorems.Thm_OAI_UniversalTensorSquare_sg33061
import Theorems.Thm_OAI_UniversalTensorSquare_sg33062
import Theorems.Thm_OAI_UniversalTensorSquare_sg33064
import Theorems.Thm_OAI_UniversalTensorSquare_sg33065
import Theorems.Thm_OAI_UniversalTensorSquare_sg33066
import Theorems.Thm_OAI_UniversalTensorSquare_sg33067
import Theorems.Thm_OAI_UniversalTensorSquare_sg33068
import Theorems.Thm_OAI_UniversalTensorSquare_sg33069
import Theorems.Thm_OAI_UniversalTensorSquare_sg33070
import Theorems.Thm_OAI_UniversalTensorSquare_sg33073
import Theorems.Thm_OAI_UniversalTensorSquare_sg33074
import Theorems.Thm_OAI_UniversalTensorSquare_sg33075
import Theorems.Thm_OAI_UniversalTensorSquare_sg33076
import Theorems.Thm_OAI_UniversalTensorSquare_sg33077
import Theorems.Thm_OAI_UniversalTensorSquare_sg33078
import Theorems.Thm_OAI_UniversalTensorSquare_sg33079
import Theorems.Thm_OAI_UniversalTensorSquare_sg4304
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

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

lemma sgCert155 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB155 sgT155) sgFlag155 = 12 := by
  decide +kernel

lemma sg155 : RowSquare [3,2,2] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB155 sgT155 sgFlag155
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB155 sgT155) sgFlag155 ≠ 0
  rw [sgCert155]
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

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

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

lemma sg762 : RowSquare [3,3,1,1,1,1] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

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

lemma sg1758 : RowSquare [6,2,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg265

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

lemma sg2699 : RowSquare [7,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

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

lemma sg4841 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1758

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

lemma sg4971 : RowSquare [9,3,3,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg155 sg1001

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

lemma sg3556 : RowSquare [8,2,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg892

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

lemma sg4307 : RowSquare [7,4,2,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg762

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16235 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4971

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

lemma sg20721 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg4841

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

lemma sg17213 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3556 sg4304

lemma sg17278 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg4307

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33059 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17278

lemma sg33063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17278

lemma sg33071 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17213

lemma sg33072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20721 sg16235

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

lemma degreeTree62_94All_oai : degreeTree62_94.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33069,⟨sg33064,⟨sg33061,⟨sg33060,⟨sg33059,True.intro,True.intro⟩,True.intro⟩,⟨sg33063,⟨sg33062,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33067,⟨sg33066,⟨sg33065,True.intro,True.intro⟩,True.intro⟩,⟨sg33068,True.intro,True.intro⟩⟩⟩,⟨sg33075,⟨sg33072,⟨sg33071,⟨sg33070,True.intro,True.intro⟩,True.intro⟩,⟨sg33074,⟨sg33073,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33078,⟨sg33077,⟨sg33076,True.intro,True.intro⟩,True.intro⟩,⟨sg33079,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_94All_oai := @OAI.UniversalTensorSquare.degreeTree62_94All_oai
