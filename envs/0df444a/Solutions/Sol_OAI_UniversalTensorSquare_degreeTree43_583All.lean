-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_583All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:09:34.654733+00:00
-- url     : https://prove2.me/submissions/5d98b88b-f71e-4db7-b1b3-607168301102

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_582All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg21139
import Theorems.Thm_OAI_UniversalTensorSquare_sg31098
import Theorems.Thm_OAI_UniversalTensorSquare_sg31100
import Theorems.Thm_OAI_UniversalTensorSquare_sg31101
import Theorems.Thm_OAI_UniversalTensorSquare_sg31102
import Theorems.Thm_OAI_UniversalTensorSquare_sg31103
import Theorems.Thm_OAI_UniversalTensorSquare_sg31104
import Theorems.Thm_OAI_UniversalTensorSquare_sg31105
import Theorems.Thm_OAI_UniversalTensorSquare_sg31106
import Theorems.Thm_OAI_UniversalTensorSquare_sg31109
import Theorems.Thm_OAI_UniversalTensorSquare_sg31110
import Theorems.Thm_OAI_UniversalTensorSquare_sg31111
import Theorems.Thm_OAI_UniversalTensorSquare_sg31112
import Theorems.Thm_OAI_UniversalTensorSquare_sg31113
import Theorems.Thm_OAI_UniversalTensorSquare_sg31114
import Theorems.Thm_OAI_UniversalTensorSquare_sg31115
import Theorems.Thm_OAI_UniversalTensorSquare_sg31117
import Theorems.Thm_OAI_UniversalTensorSquare_sg31118
import Theorems.Thm_OAI_UniversalTensorSquare_sg31119
import Theorems.Thm_OAI_UniversalTensorSquare_sg31120
import Theorems.Thm_OAI_UniversalTensorSquare_sg31121
import Theorems.Thm_OAI_UniversalTensorSquare_sg31122
import Theorems.Thm_OAI_UniversalTensorSquare_sg31123
import Theorems.Thm_OAI_UniversalTensorSquare_sg31124
import Theorems.Thm_OAI_UniversalTensorSquare_sg31125
import Theorems.Thm_OAI_UniversalTensorSquare_sg31126
import Theorems.Thm_OAI_UniversalTensorSquare_sg31127
import Theorems.Thm_OAI_UniversalTensorSquare_sg31128
import Theorems.Thm_OAI_UniversalTensorSquare_sg31129
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg958

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

lemma sgCert319 : solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB319 sgT319) sgFlag319 = -2 := by
  decide +kernel

lemma sg319 : RowSquare [4,1,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB319 sgT319 sgFlag319
  change solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB319 sgT319) sgFlag319 ≠ 0
  rw [sgCert319]
  norm_num

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

lemma sg1110 : RowSquare [7,2,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

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

lemma sg1787 : RowSquare [6,3,1,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg319

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

lemma sg5083 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1110

lemma sg5084 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,2] := by
  exact rowSquare_join (by decide) sg373 sg1110

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7780 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1754

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

lemma sg9311 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg1787

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

lemma sg9991 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5083

lemma sg9992 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,5,3] := by
  exact rowSquare_join (by decide) sg13 sg5084

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

lemma sg8801 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7780

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

lemma sg31099 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9311

lemma sg31107 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9991

lemma sg31108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9992

lemma sg31116 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg21139

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

lemma degreeTree43_581All : degreeTree43_581.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31113,⟨sg31105,⟨sg31101,⟨sg31099,⟨sg31098,True.intro,True.intro⟩,⟨sg31100,True.intro,True.intro⟩⟩,⟨sg31103,⟨sg31102,True.intro,True.intro⟩,⟨sg31104,True.intro,True.intro⟩⟩⟩,⟨sg31109,⟨sg31107,⟨sg31106,True.intro,True.intro⟩,⟨sg31108,True.intro,True.intro⟩⟩,⟨sg31111,⟨sg31110,True.intro,True.intro⟩,⟨sg31112,True.intro,True.intro⟩⟩⟩⟩,⟨sg31121,⟨sg31117,⟨sg31115,⟨sg31114,True.intro,True.intro⟩,⟨sg31116,True.intro,True.intro⟩⟩,⟨sg31119,⟨sg31118,True.intro,True.intro⟩,⟨sg31120,True.intro,True.intro⟩⟩⟩,⟨sg31125,⟨sg31123,⟨sg31122,True.intro,True.intro⟩,⟨sg31124,True.intro,True.intro⟩⟩,⟨sg31127,⟨sg31126,True.intro,True.intro⟩,⟨sg31128,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_583All_oai : degreeTree43_583.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31129,degreeTree43_581All,degreeTree43_582All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_583All_oai := @OAI.UniversalTensorSquare.degreeTree43_583All_oai
