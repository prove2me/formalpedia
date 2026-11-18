-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_616All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:03:28.022303+00:00
-- url     : https://prove2.me/submissions/301671f5-cb61-4e4c-ab3e-57d54921f3f3
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1523
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg31566
import Theorems.Thm_OAI_UniversalTensorSquare_sg31567
import Theorems.Thm_OAI_UniversalTensorSquare_sg31569
import Theorems.Thm_OAI_UniversalTensorSquare_sg31574
import Theorems.Thm_OAI_UniversalTensorSquare_sg31575
import Theorems.Thm_OAI_UniversalTensorSquare_sg31577
import Theorems.Thm_OAI_UniversalTensorSquare_sg31578
import Theorems.Thm_OAI_UniversalTensorSquare_sg31579
import Theorems.Thm_OAI_UniversalTensorSquare_sg31580
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg4930
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg942

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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
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

lemma sg448 : RowSquare [3,1,1,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg88

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg675 : RowSquare [6,1,1,1] [3,2,2,1,1] := by
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

lemma sg709 : RowSquare [7,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg88

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

lemma sg5139 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg674

lemma sg5140 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg675

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

lemma sg4583 : RowSquare [4,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,3] := by
  exact rowSquare_join (by decide) sg373 sg709

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

lemma sg6604 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg616 sg1523

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

lemma sg8166 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg942 sg1523

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

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

lemma sg10004 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg9 sg5139

lemma sg10007 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg9 sg5140

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

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

lemma sg10836 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [9,6,4,3] := by
  exact rowSquare_join (by decide) sg40 sg4583

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11543 : RowSquare [8,6,2,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg4345

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

lemma sg13500 : RowSquare [9,7,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg448 sg4930

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10007

lemma sg31570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10004

lemma sg31571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4577 sg13500

lemma sg31572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6604 sg11543

lemma sg31573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8166 sg11054

lemma sg31576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10836

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

lemma degreeTree43_616All_oai : degreeTree43_616.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31573,⟨sg31569,⟨sg31567,⟨sg31566,True.intro,True.intro⟩,⟨sg31568,True.intro,True.intro⟩⟩,⟨sg31571,⟨sg31570,True.intro,True.intro⟩,⟨sg31572,True.intro,True.intro⟩⟩⟩,⟨sg31577,⟨sg31575,⟨sg31574,True.intro,True.intro⟩,⟨sg31576,True.intro,True.intro⟩⟩,⟨sg31579,⟨sg31578,True.intro,True.intro⟩,⟨sg31580,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_616All_oai := @OAI.UniversalTensorSquare.degreeTree43_616All_oai
