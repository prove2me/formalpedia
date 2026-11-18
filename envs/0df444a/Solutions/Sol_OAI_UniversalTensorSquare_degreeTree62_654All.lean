-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_654All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:23:26.613981+00:00
-- url     : https://prove2.me/submissions/5cdaa00b-8bee-450b-8e46-aa7ebfc2f05e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg228
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg3635
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg39222
import Theorems.Thm_OAI_UniversalTensorSquare_sg39223
import Theorems.Thm_OAI_UniversalTensorSquare_sg39225
import Theorems.Thm_OAI_UniversalTensorSquare_sg39226
import Theorems.Thm_OAI_UniversalTensorSquare_sg39227
import Theorems.Thm_OAI_UniversalTensorSquare_sg39228
import Theorems.Thm_OAI_UniversalTensorSquare_sg39230
import Theorems.Thm_OAI_UniversalTensorSquare_sg39231
import Theorems.Thm_OAI_UniversalTensorSquare_sg39232
import Theorems.Thm_OAI_UniversalTensorSquare_sg39233
import Theorems.Thm_OAI_UniversalTensorSquare_sg39235
import Theorems.Thm_OAI_UniversalTensorSquare_sg39237
import Theorems.Thm_OAI_UniversalTensorSquare_sg39238
import Theorems.Thm_OAI_UniversalTensorSquare_sg39239
import Theorems.Thm_OAI_UniversalTensorSquare_sg39240
import Theorems.Thm_OAI_UniversalTensorSquare_sg39241
import Theorems.Thm_OAI_UniversalTensorSquare_sg39242
import Theorems.Thm_OAI_UniversalTensorSquare_sg483
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg940
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert143

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

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert163 : solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 = -3 := by
  decide +kernel

lemma sg163 : RowSquare [3,2,2] [4,3] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB163 sgT163 sgFlag163
  change solveCompact 7 (.full [2,2,2,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [2,2,2,1] (Equiv.refl (Fin 7)) sgB163 sgT163) sgFlag163 ≠ 0
  rw [sgCert163]
  norm_num

lemma sgCert165 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 = 15 := by
  decide +kernel

lemma sg165 : RowSquare [3,3,1] [2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [6,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB165 sgT165 sgFlag165
  change solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 ≠ 0
  rw [sgCert165]
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

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg251 : RowSquare [2,2,2,1,1] [3,3,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
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

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg519 : RowSquare [4,1,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

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

lemma sg1115 : RowSquare [7,3] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg97

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

lemma sg1202 : RowSquare [4,3,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg940

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

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6526 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1115

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

lemma sg3324 : RowSquare [6,3,3,1,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg265

lemma sg3688 : RowSquare [9,2,2,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg586

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

lemma sg4139 : RowSquare [6,4,3,3] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg143 sg483

lemma sg4231 : RowSquare [7,3,3,2,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg251

lemma sg4479 : RowSquare [9,3,1,1,1,1] [6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg228 sg519

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

lemma sg15946 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4139

lemma sg15947 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4231

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

lemma sg17506 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4479

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18587 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,8,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg6526

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

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

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

lemma sg20851 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 96. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39224 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,6,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15946

lemma sg39229 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,6,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18587

lemma sg39234 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,6,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15947

lemma sg39236 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,6,6,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17506

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

lemma degreeTree62_654All_oai : degreeTree62_654.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39232,⟨sg39227,⟨sg39224,⟨sg39223,⟨sg39222,True.intro,True.intro⟩,True.intro⟩,⟨sg39226,⟨sg39225,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39230,⟨sg39229,⟨sg39228,True.intro,True.intro⟩,True.intro⟩,⟨sg39231,True.intro,True.intro⟩⟩⟩,⟨sg39238,⟨sg39235,⟨sg39234,⟨sg39233,True.intro,True.intro⟩,True.intro⟩,⟨sg39237,⟨sg39236,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39241,⟨sg39240,⟨sg39239,True.intro,True.intro⟩,True.intro⟩,⟨sg39242,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_654All_oai := @OAI.UniversalTensorSquare.degreeTree62_654All_oai
