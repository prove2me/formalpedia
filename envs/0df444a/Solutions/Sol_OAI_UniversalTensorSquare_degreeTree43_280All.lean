-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_280All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:42.210497+00:00
-- url     : https://prove2.me/submissions/d9101b91-2844-40a5-bdf9-14d159e163c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_272All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_273All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_275All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_277All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_278All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1015
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg9850
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg465 : RowSquare [3,2,1,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg34

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg602 : RowSquare [5,1,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg315

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5543 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg590

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

lemma sg8181 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1416

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

lemma sg9846 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1755

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

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

lemma sg10861 : RowSquare [7,6,2,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg465 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12630 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg4160

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8181 sg10861

lemma sg27193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5543 sg12630

lemma sg27225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9850

lemma sg27257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,5,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9846

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

lemma degreeTree43_274All : degreeTree43_274.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27177,degreeTree43_272All,degreeTree43_273All⟩

lemma degreeTree43_276All : degreeTree43_276.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27193,degreeTree43_274All,degreeTree43_275All⟩

lemma degreeTree43_279All : degreeTree43_279.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27257,degreeTree43_277All,degreeTree43_278All⟩

lemma degreeTree43_280All_oai : degreeTree43_280.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27225,degreeTree43_276All,degreeTree43_279All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_280All_oai := @OAI.UniversalTensorSquare.degreeTree43_280All_oai
