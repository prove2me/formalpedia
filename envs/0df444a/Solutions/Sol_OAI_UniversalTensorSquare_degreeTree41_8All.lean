-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree41_8All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T18:34:46.608734+00:00
-- url     : https://prove2.me/submissions/3de7d801-9fb5-4159-b3b9-e49e319865f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg23622
import Theorems.Thm_OAI_UniversalTensorSquare_sg23623
import Theorems.Thm_OAI_UniversalTensorSquare_sg23624
import Theorems.Thm_OAI_UniversalTensorSquare_sg23625
import Theorems.Thm_OAI_UniversalTensorSquare_sg23626
import Theorems.Thm_OAI_UniversalTensorSquare_sg23627
import Theorems.Thm_OAI_UniversalTensorSquare_sg23629
import Theorems.Thm_OAI_UniversalTensorSquare_sg23630
import Theorems.Thm_OAI_UniversalTensorSquare_sg23631
import Theorems.Thm_OAI_UniversalTensorSquare_sg23632
import Theorems.Thm_OAI_UniversalTensorSquare_sg23633
import Theorems.Thm_OAI_UniversalTensorSquare_sg23634
import Theorems.Thm_OAI_UniversalTensorSquare_sg23635
import Theorems.Thm_OAI_UniversalTensorSquare_sg23636
import Theorems.Thm_OAI_UniversalTensorSquare_sg23637
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sgCert10 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 = -2 := by
  decide +kernel

lemma sg10 : RowSquare [2,1,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB10 sgT10 sgFlag10
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 ≠ 0
  rw [sgCert10]
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

lemma sg396 : RowSquare [5,2,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg10

lemma sg639 : RowSquare [5,2,2] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg32

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

lemma sg4579 : RowSquare [3,3,3,2,1,1,1,1,1,1] [7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg639

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

lemma sg8406 : RowSquare [5,5,3,2,1,1,1,1,1,1] [8,8,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4579

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7512 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23628 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7512 sg8406

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree41_8All_oai : degreeTree41_8.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23630,⟨sg23626,⟨sg23624,⟨sg23623,⟨sg23622,True.intro,True.intro⟩,True.intro⟩,⟨sg23625,True.intro,True.intro⟩⟩,⟨sg23628,⟨sg23627,True.intro,True.intro⟩,⟨sg23629,True.intro,True.intro⟩⟩⟩,⟨sg23634,⟨sg23632,⟨sg23631,True.intro,True.intro⟩,⟨sg23633,True.intro,True.intro⟩⟩,⟨sg23636,⟨sg23635,True.intro,True.intro⟩,⟨sg23637,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree41_8All_oai := @OAI.UniversalTensorSquare.degreeTree41_8All_oai
