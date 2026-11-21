-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree26_35All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:59:32.293313+00:00
-- url     : https://prove2.me/submissions/3cabb584-e17b-45b8-9578-8f20cc50311b

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13287
import Theorems.Thm_OAI_UniversalTensorSquare_sg13288
import Theorems.Thm_OAI_UniversalTensorSquare_sg13289
import Theorems.Thm_OAI_UniversalTensorSquare_sg13290
import Theorems.Thm_OAI_UniversalTensorSquare_sg13292
import Theorems.Thm_OAI_UniversalTensorSquare_sg13293
import Theorems.Thm_OAI_UniversalTensorSquare_sg13294
import Theorems.Thm_OAI_UniversalTensorSquare_sg13296
import Theorems.Thm_OAI_UniversalTensorSquare_sg13299
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg61
import Theorems.Thm_OAI_UniversalTensorSquare_sg636

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

lemma sgCert17 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 = -2 := by
  decide +kernel

lemma sg17 : RowSquare [3,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB17 sgT17 sgFlag17
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 ≠ 0
  rw [sgCert17]
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

lemma sg212 : RowSquare [4,3] [4,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg215 : RowSquare [4,3] [5,2] := by
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

lemma sg23 : RowSquare [2,1,1,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg70 : RowSquare [3,1,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

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

lemma sg1149 : RowSquare [3,3,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg636

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

lemma sg1592 : RowSquare [3,3,1,1,1,1,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg87

lemma sg1651 : RowSquare [4,4,2,2] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg61

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

lemma sg2593 : RowSquare [5,4,1,1,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg586

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

lemma sg3282 : RowSquare [5,4,1,1,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg586

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

lemma sg5930 : RowSquare [4,4,2,2,2,2,2,1] [5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg1650

lemma sg5931 : RowSquare [4,4,2,2,2,2,2,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1651

lemma sg5941 : RowSquare [4,4,2,2,2,2,2,1] [6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg1650

lemma sg5942 : RowSquare [4,4,2,2,2,2,2,1] [6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg1651

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

lemma sg13286 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5941

lemma sg13291 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5931

lemma sg13295 : RowSquare [8,7,2,2,2,2,2,1] [8,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1592 sg2593

lemma sg13297 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5930

lemma sg13298 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5942

lemma sg13300 : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3282

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

lemma degreeTree26_35All_oai : degreeTree26_35.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13293,⟨sg13289,⟨sg13287,⟨sg13286,True.intro,True.intro⟩,⟨sg13288,True.intro,True.intro⟩⟩,⟨sg13291,⟨sg13290,True.intro,True.intro⟩,⟨sg13292,True.intro,True.intro⟩⟩⟩,⟨sg13297,⟨sg13295,⟨sg13294,True.intro,True.intro⟩,⟨sg13296,True.intro,True.intro⟩⟩,⟨sg13299,⟨sg13298,True.intro,True.intro⟩,⟨sg13300,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree26_35All_oai := @OAI.UniversalTensorSquare.degreeTree26_35All_oai
