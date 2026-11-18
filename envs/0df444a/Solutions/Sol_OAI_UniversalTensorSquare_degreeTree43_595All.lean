-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_595All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:26.245245+00:00
-- url     : https://prove2.me/submissions/8c382deb-67ff-4ed7-9378-791c2fd770dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10501
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg31291
import Theorems.Thm_OAI_UniversalTensorSquare_sg31292
import Theorems.Thm_OAI_UniversalTensorSquare_sg31293
import Theorems.Thm_OAI_UniversalTensorSquare_sg31294
import Theorems.Thm_OAI_UniversalTensorSquare_sg31296
import Theorems.Thm_OAI_UniversalTensorSquare_sg31298
import Theorems.Thm_OAI_UniversalTensorSquare_sg31299
import Theorems.Thm_OAI_UniversalTensorSquare_sg31300
import Theorems.Thm_OAI_UniversalTensorSquare_sg31302
import Theorems.Thm_OAI_UniversalTensorSquare_sg31303
import Theorems.Thm_OAI_UniversalTensorSquare_sg31304
import Theorems.Thm_OAI_UniversalTensorSquare_sg31305
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg541
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg9300
import Theorems.Thm_OAI_UniversalTensorSquare_sg9850
import Theorems.Thm_OAI_UniversalTensorSquare_sg9981

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

lemma sgCert275 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 = -1 := by
  decide +kernel

lemma sg275 : RowSquare [3,2,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB275 sgT275 sgFlag275
  change solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 ≠ 0
  rw [sgCert275]
  norm_num

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

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8657 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1754

lemma sg8815 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg2251

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

lemma sg31295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10501

lemma sg31297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9300

lemma sg31301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9981

lemma sg31306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9850

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

lemma degreeTree43_595All_oai : degreeTree43_595.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31299,⟨sg31295,⟨sg31293,⟨sg31292,⟨sg31291,True.intro,True.intro⟩,True.intro⟩,⟨sg31294,True.intro,True.intro⟩⟩,⟨sg31297,⟨sg31296,True.intro,True.intro⟩,⟨sg31298,True.intro,True.intro⟩⟩⟩,⟨sg31303,⟨sg31301,⟨sg31300,True.intro,True.intro⟩,⟨sg31302,True.intro,True.intro⟩⟩,⟨sg31305,⟨sg31304,True.intro,True.intro⟩,⟨sg31306,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_595All_oai := @OAI.UniversalTensorSquare.degreeTree43_595All_oai
