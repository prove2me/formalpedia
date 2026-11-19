-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree26_18All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:11:13.324236+00:00
-- url     : https://prove2.me/submissions/c11d4aa8-db41-4b6c-87cb-f82536bd502a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg13137
import Theorems.Thm_OAI_UniversalTensorSquare_sg13139
import Theorems.Thm_OAI_UniversalTensorSquare_sg13141
import Theorems.Thm_OAI_UniversalTensorSquare_sg13148
import Theorems.Thm_OAI_UniversalTensorSquare_sg13150
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2063
import Theorems.Thm_OAI_UniversalTensorSquare_sg2547
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg474
import Theorems.Thm_OAI_UniversalTensorSquare_sg490
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg61
import Theorems.Thm_OAI_UniversalTensorSquare_sg67
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg71
import Theorems.Thm_OAI_UniversalTensorSquare_sg87
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert1063
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1063 : RowSquare [6,2,2] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1063 sgT1063 sgFlag1063
  change solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1063 sgT1063) sgFlag1063 ≠ 0
  rw [sgCert1063]
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

lemma sg59 : RowSquare [2,2,1,1] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg60 : RowSquare [2,2,1,1] [5,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg208 : RowSquare [4,3] [3,2,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg209 : RowSquare [4,3] [3,2,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg210 : RowSquare [4,3] [3,3,1] := by
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

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg70 : RowSquare [3,1,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

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

lemma sg1146 : RowSquare [3,3,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg87

lemma sg1147 : RowSquare [3,3,1,1,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg88

lemma sg1151 : RowSquare [3,3,1,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1063

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

lemma sg1640 : RowSquare [4,3,1,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg371

lemma sg1651 : RowSquare [4,4,2,2] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg61

lemma sg1652 : RowSquare [4,4,2,2] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg61

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

lemma sg2053 : RowSquare [4,3,1,1,1,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg178

lemma sg2082 : RowSquare [4,4,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg66 sg178

lemma sg2084 : RowSquare [4,4,1,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg178

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

lemma sg3276 : RowSquare [5,4,1,1,1,1,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg586

lemma sg3278 : RowSquare [5,4,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg586

lemma sg3282 : RowSquare [5,4,1,1,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg586

lemma sg3287 : RowSquare [5,4,1,1,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg586

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

lemma sg5706 : RowSquare [6,5,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg474

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

lemma sg5927 : RowSquare [4,4,2,2,2,2,2,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1650

lemma sg5935 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1651

lemma sg5936 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1652

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

lemma sg10067 : RowSquare [6,5,2,2,2,2,2,1] [6,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5706

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13138 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10067

lemma sg13140 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3276

lemma sg13142 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1146 sg3287

lemma sg13143 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2084 sg2063

lemma sg13144 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2082 sg2053

lemma sg13145 : RowSquare [8,7,2,2,2,2,2,1] [7,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1640 sg2547

lemma sg13146 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5927

lemma sg13147 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5935

lemma sg13149 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1151 sg3278

lemma sg13151 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5936

lemma sg13152 : RowSquare [8,7,2,2,2,2,2,1] [7,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3282

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree26_18All_oai : degreeTree26_18.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13145,⟨sg13141,⟨sg13139,⟨sg13138,⟨sg13137,True.intro,True.intro⟩,True.intro⟩,⟨sg13140,True.intro,True.intro⟩⟩,⟨sg13143,⟨sg13142,True.intro,True.intro⟩,⟨sg13144,True.intro,True.intro⟩⟩⟩,⟨sg13149,⟨sg13147,⟨sg13146,True.intro,True.intro⟩,⟨sg13148,True.intro,True.intro⟩⟩,⟨sg13151,⟨sg13150,True.intro,True.intro⟩,⟨sg13152,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree26_18All_oai := @OAI.UniversalTensorSquare.degreeTree26_18All_oai
