-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_95All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:06:46.927343+00:00
-- url     : https://prove2.me/submissions/7fe2d1e2-bdd7-45e7-9a04-31382314b84b
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg12688
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg24872
import Theorems.Thm_OAI_UniversalTensorSquare_sg24874
import Theorems.Thm_OAI_UniversalTensorSquare_sg24875
import Theorems.Thm_OAI_UniversalTensorSquare_sg24876
import Theorems.Thm_OAI_UniversalTensorSquare_sg24878
import Theorems.Thm_OAI_UniversalTensorSquare_sg24879
import Theorems.Thm_OAI_UniversalTensorSquare_sg24880
import Theorems.Thm_OAI_UniversalTensorSquare_sg24881
import Theorems.Thm_OAI_UniversalTensorSquare_sg24882
import Theorems.Thm_OAI_UniversalTensorSquare_sg24883
import Theorems.Thm_OAI_UniversalTensorSquare_sg24884
import Theorems.Thm_OAI_UniversalTensorSquare_sg24885
import Theorems.Thm_OAI_UniversalTensorSquare_sg24886
import Theorems.Thm_OAI_UniversalTensorSquare_sg24887
import Theorems.Thm_OAI_UniversalTensorSquare_sg24888
import Theorems.Thm_OAI_UniversalTensorSquare_sg24889
import Theorems.Thm_OAI_UniversalTensorSquare_sg24891
import Theorems.Thm_OAI_UniversalTensorSquare_sg24892
import Theorems.Thm_OAI_UniversalTensorSquare_sg24893
import Theorems.Thm_OAI_UniversalTensorSquare_sg24895
import Theorems.Thm_OAI_UniversalTensorSquare_sg24896
import Theorems.Thm_OAI_UniversalTensorSquare_sg24897
import Theorems.Thm_OAI_UniversalTensorSquare_sg24898
import Theorems.Thm_OAI_UniversalTensorSquare_sg24899
import Theorems.Thm_OAI_UniversalTensorSquare_sg24900
import Theorems.Thm_OAI_UniversalTensorSquare_sg24901
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg9510
import Theorems.Thm_OAI_UniversalTensorSquare_sg960

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

lemma sgCert320 : solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB320 sgT320) sgFlag320 = 4 := by
  decide +kernel

lemma sg320 : RowSquare [4,1,1,1,1] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB320 sgT320 sgFlag320
  change solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB320 sgT320) sgFlag320 ≠ 0
  rw [sgCert320]
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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg92

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg596 : RowSquare [5,1,1,1,1] [3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg320

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2254 : RowSquare [7,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg451

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

lemma sg5248 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg960

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

lemma sg8349 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1682

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

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

lemma sg10648 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2254

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

lemma sg9509 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1041 sg1755

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8349 sg10648

lemma sg24873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5248 sg12688

lemma sg24877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9509

lemma sg24890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9509

lemma sg24894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9510

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

lemma degreeTree43_95All_oai : degreeTree43_95.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24886,⟨sg24878,⟨sg24874,⟨sg24872,⟨sg24871,True.intro,True.intro⟩,⟨sg24873,True.intro,True.intro⟩⟩,⟨sg24876,⟨sg24875,True.intro,True.intro⟩,⟨sg24877,True.intro,True.intro⟩⟩⟩,⟨sg24882,⟨sg24880,⟨sg24879,True.intro,True.intro⟩,⟨sg24881,True.intro,True.intro⟩⟩,⟨sg24884,⟨sg24883,True.intro,True.intro⟩,⟨sg24885,True.intro,True.intro⟩⟩⟩⟩,⟨sg24894,⟨sg24890,⟨sg24888,⟨sg24887,True.intro,True.intro⟩,⟨sg24889,True.intro,True.intro⟩⟩,⟨sg24892,⟨sg24891,True.intro,True.intro⟩,⟨sg24893,True.intro,True.intro⟩⟩⟩,⟨sg24898,⟨sg24896,⟨sg24895,True.intro,True.intro⟩,⟨sg24897,True.intro,True.intro⟩⟩,⟨sg24900,⟨sg24899,True.intro,True.intro⟩,⟨sg24901,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_95All_oai := @OAI.UniversalTensorSquare.degreeTree43_95All_oai
