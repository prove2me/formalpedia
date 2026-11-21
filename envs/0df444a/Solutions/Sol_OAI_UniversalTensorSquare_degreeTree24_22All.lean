-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_22All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:22.116171+00:00
-- url     : https://prove2.me/submissions/0151c066-9611-4694-8acb-1a946afa5aa3

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg12210
import Theorems.Thm_OAI_UniversalTensorSquare_sg12211
import Theorems.Thm_OAI_UniversalTensorSquare_sg12212
import Theorems.Thm_OAI_UniversalTensorSquare_sg12214
import Theorems.Thm_OAI_UniversalTensorSquare_sg12216
import Theorems.Thm_OAI_UniversalTensorSquare_sg12217
import Theorems.Thm_OAI_UniversalTensorSquare_sg12218
import Theorems.Thm_OAI_UniversalTensorSquare_sg12219
import Theorems.Thm_OAI_UniversalTensorSquare_sg12220
import Theorems.Thm_OAI_UniversalTensorSquare_sg12221
import Theorems.Thm_OAI_UniversalTensorSquare_sg12222
import Theorems.Thm_OAI_UniversalTensorSquare_sg12223
import Theorems.Thm_OAI_UniversalTensorSquare_sg12224
import Theorems.Thm_OAI_UniversalTensorSquare_sg12225
import Theorems.Thm_OAI_UniversalTensorSquare_sg12226
import Theorems.Thm_OAI_UniversalTensorSquare_sg12227
import Theorems.Thm_OAI_UniversalTensorSquare_sg12228
import Theorems.Thm_OAI_UniversalTensorSquare_sg12229
import Theorems.Thm_OAI_UniversalTensorSquare_sg12231
import Theorems.Thm_OAI_UniversalTensorSquare_sg12232
import Theorems.Thm_OAI_UniversalTensorSquare_sg12233
import Theorems.Thm_OAI_UniversalTensorSquare_sg12234
import Theorems.Thm_OAI_UniversalTensorSquare_sg12236
import Theorems.Thm_OAI_UniversalTensorSquare_sg12238
import Theorems.Thm_OAI_UniversalTensorSquare_sg12239
import Theorems.Thm_OAI_UniversalTensorSquare_sg2583
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg776
import Theorems.Thm_OAI_UniversalTensorSquare_sg89

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

lemma sgCert88 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 = 8 := by
  decide +kernel

lemma sg88 : RowSquare [4,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB88 sgT88 sgFlag88
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 ≠ 0
  rw [sgCert88]
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

lemma sg770 : RowSquare [3,3,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg33 sg33

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

lemma sg1593 : RowSquare [3,3,1,1,1,1,1,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg88

lemma sg1594 : RowSquare [3,3,1,1,1,1,1,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg89

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

lemma sg1678 : RowSquare [5,3,1,1,1,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg586

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

lemma sg2577 : RowSquare [5,3,1,1,1,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12213 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg776 sg2577

lemma sg12215 : RowSquare [8,6,2,2,2,2,1,1] [8,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1592

lemma sg12230 : RowSquare [8,6,2,2,2,2,1,1] [8,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1593

lemma sg12235 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1678 sg1594

lemma sg12237 : RowSquare [8,6,2,2,2,2,1,1] [8,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg2583

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree24_22All_oai : degreeTree24_22.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12225,⟨sg12217,⟨sg12213,⟨sg12211,⟨sg12210,True.intro,True.intro⟩,⟨sg12212,True.intro,True.intro⟩⟩,⟨sg12215,⟨sg12214,True.intro,True.intro⟩,⟨sg12216,True.intro,True.intro⟩⟩⟩,⟨sg12221,⟨sg12219,⟨sg12218,True.intro,True.intro⟩,⟨sg12220,True.intro,True.intro⟩⟩,⟨sg12223,⟨sg12222,True.intro,True.intro⟩,⟨sg12224,True.intro,True.intro⟩⟩⟩⟩,⟨sg12233,⟨sg12229,⟨sg12227,⟨sg12226,True.intro,True.intro⟩,⟨sg12228,True.intro,True.intro⟩⟩,⟨sg12231,⟨sg12230,True.intro,True.intro⟩,⟨sg12232,True.intro,True.intro⟩⟩⟩,⟨sg12237,⟨sg12235,⟨sg12234,True.intro,True.intro⟩,⟨sg12236,True.intro,True.intro⟩⟩,⟨sg12239,⟨sg12238,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_22All_oai := @OAI.UniversalTensorSquare.degreeTree24_22All_oai
