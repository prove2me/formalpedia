-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_875All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:26:21.205606+00:00
-- url     : https://prove2.me/submissions/6afb3922-5d03-46c6-b1ad-22e17f8d2dc2
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2617
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg41656
import Theorems.Thm_OAI_UniversalTensorSquare_sg41658
import Theorems.Thm_OAI_UniversalTensorSquare_sg41659
import Theorems.Thm_OAI_UniversalTensorSquare_sg41661
import Theorems.Thm_OAI_UniversalTensorSquare_sg41662
import Theorems.Thm_OAI_UniversalTensorSquare_sg41664
import Theorems.Thm_OAI_UniversalTensorSquare_sg41665
import Theorems.Thm_OAI_UniversalTensorSquare_sg41666
import Theorems.Thm_OAI_UniversalTensorSquare_sg41667
import Theorems.Thm_OAI_UniversalTensorSquare_sg41668
import Theorems.Thm_OAI_UniversalTensorSquare_sg41669
import Theorems.Thm_OAI_UniversalTensorSquare_sg41670
import Theorems.Thm_OAI_UniversalTensorSquare_sg41672
import Theorems.Thm_OAI_UniversalTensorSquare_sg41674
import Theorems.Thm_OAI_UniversalTensorSquare_sg41675
import Theorems.Thm_OAI_UniversalTensorSquare_sg41676
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg703
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg998
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1134 : RowSquare [2,2,2,2,2,1] [4,4,2,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1135 : RowSquare [2,2,2,2,2,1] [4,4,3] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
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

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1092 : RowSquare [7,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg178

lemma sg1094 : RowSquare [7,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg372

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

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

lemma sg4524 : RowSquare [10,2,2,2] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg372

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

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6709 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1092

lemma sg6710 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1094

lemma sg6711 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1092

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15452 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2617 sg4524

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

lemma sg16075 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15452

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

lemma sg18808 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1135 sg6709

lemma sg18809 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1134 sg6710

lemma sg18811 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1134 sg6711

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

lemma sg20314 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg5737

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

lemma sg41657 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,5,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18808

lemma sg41660 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,6,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18811

lemma sg41663 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,6,5,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18809

lemma sg41671 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,6,5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18811

lemma sg41673 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,6,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16075

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

lemma degreeTree62_875All_oai : degreeTree62_875.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41666,⟨sg41661,⟨sg41658,⟨sg41657,⟨sg41656,True.intro,True.intro⟩,True.intro⟩,⟨sg41660,⟨sg41659,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41664,⟨sg41663,⟨sg41662,True.intro,True.intro⟩,True.intro⟩,⟨sg41665,True.intro,True.intro⟩⟩⟩,⟨sg41672,⟨sg41669,⟨sg41668,⟨sg41667,True.intro,True.intro⟩,True.intro⟩,⟨sg41671,⟨sg41670,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41675,⟨sg41674,⟨sg41673,True.intro,True.intro⟩,True.intro⟩,⟨sg41676,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_875All_oai := @OAI.UniversalTensorSquare.degreeTree62_875All_oai
