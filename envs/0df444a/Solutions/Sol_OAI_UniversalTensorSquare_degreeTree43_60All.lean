-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_60All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:19:53.286222+00:00
-- url     : https://prove2.me/submissions/0d8139ec-c741-41d1-844f-960fd70b3231
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10098
import Theorems.Thm_OAI_UniversalTensorSquare_sg10227
import Theorems.Thm_OAI_UniversalTensorSquare_sg10228
import Theorems.Thm_OAI_UniversalTensorSquare_sg10229
import Theorems.Thm_OAI_UniversalTensorSquare_sg10639
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg24450
import Theorems.Thm_OAI_UniversalTensorSquare_sg24451
import Theorems.Thm_OAI_UniversalTensorSquare_sg24452
import Theorems.Thm_OAI_UniversalTensorSquare_sg24453
import Theorems.Thm_OAI_UniversalTensorSquare_sg24454
import Theorems.Thm_OAI_UniversalTensorSquare_sg24456
import Theorems.Thm_OAI_UniversalTensorSquare_sg24457
import Theorems.Thm_OAI_UniversalTensorSquare_sg24462
import Theorems.Thm_OAI_UniversalTensorSquare_sg24464
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg9492
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert548

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

lemma sg548 : RowSquare [4,2,2,1] [2,1,1,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [8,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB548 sgT548 sgFlag548
  change solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 ≠ 0
  rw [sgCert548]
  norm_num

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

lemma sg1758 : RowSquare [6,2,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg265

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

lemma sg8450 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg548 sg1758

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10193 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1331

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

lemma sg8539 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1331

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10228

lemma sg24458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9492

lemma sg24459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10229

lemma sg24460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10639

lemma sg24461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10227

lemma sg24463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,4,1] := by
  exact rowSquare_join (by decide) sg8450 sg10193

lemma sg24465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8539 sg10098

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

lemma degreeTree43_60All_oai : degreeTree43_60.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24458,⟨sg24454,⟨sg24452,⟨sg24451,⟨sg24450,True.intro,True.intro⟩,True.intro⟩,⟨sg24453,True.intro,True.intro⟩⟩,⟨sg24456,⟨sg24455,True.intro,True.intro⟩,⟨sg24457,True.intro,True.intro⟩⟩⟩,⟨sg24462,⟨sg24460,⟨sg24459,True.intro,True.intro⟩,⟨sg24461,True.intro,True.intro⟩⟩,⟨sg24464,⟨sg24463,True.intro,True.intro⟩,⟨sg24465,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_60All_oai := @OAI.UniversalTensorSquare.degreeTree43_60All_oai
