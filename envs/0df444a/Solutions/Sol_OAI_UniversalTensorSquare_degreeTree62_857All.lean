-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_857All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:26:12.822219+00:00
-- url     : https://prove2.me/submissions/ef3b5a82-d814-47e9-a28b-e6bc01bff67a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_851All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_852All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_854All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_855All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512
import Theorems.Thm_OAI_UniversalTensorSquare_sg2752
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg41436
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg915

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

lemma sgCert490 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 = 2 := by
  decide +kernel

lemma sg490 : RowSquare [3,3,1,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB490 sgT490 sgFlag490
  change solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 ≠ 0
  rw [sgCert490]
  norm_num

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

lemma sg1502 : RowSquare [7,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1001

lemma sg1555 : RowSquare [8,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg373

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

lemma sg3622 : RowSquare [8,3,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg915

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14947 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2752 sg3622

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17710 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14947

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

lemma sg8956 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1502 sg1555

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

lemma sg20077 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,6,3] := by
  exact rowSquare_join (by decide) sg490 sg8956

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 102. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41414 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,8,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17710

lemma sg41458 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,9,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20077

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

lemma degreeTree62_853All : degreeTree62_853.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41414,degreeTree62_851All,degreeTree62_852All⟩

lemma degreeTree62_856All : degreeTree62_856.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41458,degreeTree62_854All,degreeTree62_855All⟩

lemma degreeTree62_857All_oai : degreeTree62_857.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41436,degreeTree62_853All,degreeTree62_856All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_857All_oai := @OAI.UniversalTensorSquare.degreeTree62_857All_oai
