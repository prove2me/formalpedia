-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_630All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:01:05.45756+00:00
-- url     : https://prove2.me/submissions/cb2db7f4-05a0-47c8-be94-2a67044a75ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg31743
import Theorems.Thm_OAI_UniversalTensorSquare_sg31744
import Theorems.Thm_OAI_UniversalTensorSquare_sg31746
import Theorems.Thm_OAI_UniversalTensorSquare_sg31748
import Theorems.Thm_OAI_UniversalTensorSquare_sg31749
import Theorems.Thm_OAI_UniversalTensorSquare_sg31751
import Theorems.Thm_OAI_UniversalTensorSquare_sg31752
import Theorems.Thm_OAI_UniversalTensorSquare_sg31753
import Theorems.Thm_OAI_UniversalTensorSquare_sg31754
import Theorems.Thm_OAI_UniversalTensorSquare_sg31755
import Theorems.Thm_OAI_UniversalTensorSquare_sg31756
import Theorems.Thm_OAI_UniversalTensorSquare_sg31757
import Theorems.Thm_OAI_UniversalTensorSquare_sg31758
import Theorems.Thm_OAI_UniversalTensorSquare_sg31759
import Theorems.Thm_OAI_UniversalTensorSquare_sg31760
import Theorems.Thm_OAI_UniversalTensorSquare_sg31761
import Theorems.Thm_OAI_UniversalTensorSquare_sg31762
import Theorems.Thm_OAI_UniversalTensorSquare_sg31763
import Theorems.Thm_OAI_UniversalTensorSquare_sg31764
import Theorems.Thm_OAI_UniversalTensorSquare_sg31765
import Theorems.Thm_OAI_UniversalTensorSquare_sg31767
import Theorems.Thm_OAI_UniversalTensorSquare_sg31768
import Theorems.Thm_OAI_UniversalTensorSquare_sg31770
import Theorems.Thm_OAI_UniversalTensorSquare_sg31771
import Theorems.Thm_OAI_UniversalTensorSquare_sg31772
import Theorems.Thm_OAI_UniversalTensorSquare_sg31773
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4930
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert640 : solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB640 sgT640) sgFlag640 = -1 := by
  decide +kernel

lemma sg640 : RowSquare [5,2,2] [3,3,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB640 sgT640 sgFlag640
  change solveCompact 9 (.full [4,3,2]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [4,3,2] (Equiv.refl (Fin 9)) sgB640 sgT640) sgFlag640 ≠ 0
  rw [sgCert640]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert377 : solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 = -4 := by
  decide +kernel

lemma sg377 : RowSquare [5,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB377 sgT377 sgFlag377
  change solveCompact 8 (.full [4,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB377 sgT377) sgFlag377 ≠ 0
  rw [sgCert377]
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

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg137 : RowSquare [3,1,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg414 : RowSquare [6,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg88

lemma sg450 : RowSquare [3,1,1,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg20 sg34

lemma sg533 : RowSquare [4,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg0 sg265

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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1406 : RowSquare [6,2,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg17 sg137

lemma sg1415 : RowSquare [6,2,2,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg33 sg68

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3748 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,4,2,2] := by
  exact rowSquare_join (by decide) sg414 sg414

lemma sg3893 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg377

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

lemma sg4577 : RowSquare [3,3,3,2,1,1,1,1,1,1] [5,5,4,3] := by
  exact rowSquare_join (by decide) sg390 sg640

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

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8169 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1415

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

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

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10840 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [10,6,4,2] := by
  exact rowSquare_join (by decide) sg97 sg3748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13502 : RowSquare [9,7,1,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg450 sg4930

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9410 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1406

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11054 : RowSquare [8,6,1,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg3521

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14523 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg533 sg5735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4577 sg13502

lemma sg31747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8169 sg11054

lemma sg31750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10840

lemma sg31766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3893 sg14523

lemma sg31769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9410

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

lemma degreeTree43_630All_oai : degreeTree43_630.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31758,⟨sg31750,⟨sg31746,⟨sg31744,⟨sg31743,True.intro,True.intro⟩,⟨sg31745,True.intro,True.intro⟩⟩,⟨sg31748,⟨sg31747,True.intro,True.intro⟩,⟨sg31749,True.intro,True.intro⟩⟩⟩,⟨sg31754,⟨sg31752,⟨sg31751,True.intro,True.intro⟩,⟨sg31753,True.intro,True.intro⟩⟩,⟨sg31756,⟨sg31755,True.intro,True.intro⟩,⟨sg31757,True.intro,True.intro⟩⟩⟩⟩,⟨sg31766,⟨sg31762,⟨sg31760,⟨sg31759,True.intro,True.intro⟩,⟨sg31761,True.intro,True.intro⟩⟩,⟨sg31764,⟨sg31763,True.intro,True.intro⟩,⟨sg31765,True.intro,True.intro⟩⟩⟩,⟨sg31770,⟨sg31768,⟨sg31767,True.intro,True.intro⟩,⟨sg31769,True.intro,True.intro⟩⟩,⟨sg31772,⟨sg31771,True.intro,True.intro⟩,⟨sg31773,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_630All_oai := @OAI.UniversalTensorSquare.degreeTree43_630All_oai
