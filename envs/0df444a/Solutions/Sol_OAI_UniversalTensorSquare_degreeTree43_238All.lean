-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_238All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:20:41.825701+00:00
-- url     : https://prove2.me/submissions/4452cd91-66c5-439b-9f02-ec5074324568
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10304
import Theorems.Thm_OAI_UniversalTensorSquare_sg10305
import Theorems.Thm_OAI_UniversalTensorSquare_sg10306
import Theorems.Thm_OAI_UniversalTensorSquare_sg10307
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg26742
import Theorems.Thm_OAI_UniversalTensorSquare_sg26745
import Theorems.Thm_OAI_UniversalTensorSquare_sg26746
import Theorems.Thm_OAI_UniversalTensorSquare_sg26747
import Theorems.Thm_OAI_UniversalTensorSquare_sg26750
import Theorems.Thm_OAI_UniversalTensorSquare_sg26751
import Theorems.Thm_OAI_UniversalTensorSquare_sg26752
import Theorems.Thm_OAI_UniversalTensorSquare_sg26753
import Theorems.Thm_OAI_UniversalTensorSquare_sg26755
import Theorems.Thm_OAI_UniversalTensorSquare_sg26756
import Theorems.Thm_OAI_UniversalTensorSquare_sg26757
import Theorems.Thm_OAI_UniversalTensorSquare_sg26758
import Theorems.Thm_OAI_UniversalTensorSquare_sg26759
import Theorems.Thm_OAI_UniversalTensorSquare_sg26760
import Theorems.Thm_OAI_UniversalTensorSquare_sg26762
import Theorems.Thm_OAI_UniversalTensorSquare_sg26763
import Theorems.Thm_OAI_UniversalTensorSquare_sg26764
import Theorems.Thm_OAI_UniversalTensorSquare_sg26765
import Theorems.Thm_OAI_UniversalTensorSquare_sg26766
import Theorems.Thm_OAI_UniversalTensorSquare_sg26769
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg8535
import Theorems.Thm_OAI_UniversalTensorSquare_sg9215
import Theorems.Thm_OAI_UniversalTensorSquare_sg9569
import Theorems.Thm_OAI_UniversalTensorSquare_sg9570
import Theorems.Thm_OAI_UniversalTensorSquare_sg9833
import Theorems.Thm_OAI_UniversalTensorSquare_sg9835
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

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

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

lemma sg1003 : RowSquare [6,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg588

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

lemma sg1647 : RowSquare [4,3,2,1,1,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg143

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

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

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

lemma sg9280 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1782

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

lemma sg10115 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1647

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10115

lemma sg26744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10304

lemma sg26748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9280

lemma sg26749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9215

lemma sg26754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9833

lemma sg26761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10305

lemma sg26767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9569

lemma sg26768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10306

lemma sg26770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9835

lemma sg26771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9570

lemma sg26772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10307

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

lemma degreeTree43_238All_oai : degreeTree43_238.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26757,⟨sg26749,⟨sg26745,⟨sg26743,⟨sg26742,True.intro,True.intro⟩,⟨sg26744,True.intro,True.intro⟩⟩,⟨sg26747,⟨sg26746,True.intro,True.intro⟩,⟨sg26748,True.intro,True.intro⟩⟩⟩,⟨sg26753,⟨sg26751,⟨sg26750,True.intro,True.intro⟩,⟨sg26752,True.intro,True.intro⟩⟩,⟨sg26755,⟨sg26754,True.intro,True.intro⟩,⟨sg26756,True.intro,True.intro⟩⟩⟩⟩,⟨sg26765,⟨sg26761,⟨sg26759,⟨sg26758,True.intro,True.intro⟩,⟨sg26760,True.intro,True.intro⟩⟩,⟨sg26763,⟨sg26762,True.intro,True.intro⟩,⟨sg26764,True.intro,True.intro⟩⟩⟩,⟨sg26769,⟨sg26767,⟨sg26766,True.intro,True.intro⟩,⟨sg26768,True.intro,True.intro⟩⟩,⟨sg26771,⟨sg26770,True.intro,True.intro⟩,⟨sg26772,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_238All_oai := @OAI.UniversalTensorSquare.degreeTree43_238All_oai
