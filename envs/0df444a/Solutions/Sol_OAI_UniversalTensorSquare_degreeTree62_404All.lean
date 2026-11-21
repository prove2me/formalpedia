-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_404All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:18:32.039387+00:00
-- url     : https://prove2.me/submissions/5d0bd0dc-c23a-4c29-88c0-9eca3dd048bb

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg1762
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg36481
import Theorems.Thm_OAI_UniversalTensorSquare_sg36482
import Theorems.Thm_OAI_UniversalTensorSquare_sg36484
import Theorems.Thm_OAI_UniversalTensorSquare_sg36485
import Theorems.Thm_OAI_UniversalTensorSquare_sg36486
import Theorems.Thm_OAI_UniversalTensorSquare_sg36487
import Theorems.Thm_OAI_UniversalTensorSquare_sg36488
import Theorems.Thm_OAI_UniversalTensorSquare_sg36489
import Theorems.Thm_OAI_UniversalTensorSquare_sg36490
import Theorems.Thm_OAI_UniversalTensorSquare_sg36491
import Theorems.Thm_OAI_UniversalTensorSquare_sg36492
import Theorems.Thm_OAI_UniversalTensorSquare_sg36493
import Theorems.Thm_OAI_UniversalTensorSquare_sg36495
import Theorems.Thm_OAI_UniversalTensorSquare_sg36496
import Theorems.Thm_OAI_UniversalTensorSquare_sg36497
import Theorems.Thm_OAI_UniversalTensorSquare_sg36498
import Theorems.Thm_OAI_UniversalTensorSquare_sg36499
import Theorems.Thm_OAI_UniversalTensorSquare_sg36501
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg42 : RowSquare [3,2] [3,2] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg43 : RowSquare [3,2] [4,1] := by
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

lemma sg23 : RowSquare [2,1,1,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg92

lemma sg632 : RowSquare [5,2,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg23

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

lemma sg727 : RowSquare [2,2,2,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg46 sg42

lemma sg728 : RowSquare [2,2,2,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg46 sg43

lemma sg1188 : RowSquare [4,2,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg178

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

lemma sg1499 : RowSquare [7,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg998

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

lemma sg1945 : RowSquare [8,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg998

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

lemma sg2370 : RowSquare [8,2,1,1,1] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2707 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg451

lemma sg2737 : RowSquare [7,3,1,1,1,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg1762

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

lemma sg6469 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg728

lemma sg6470 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg727

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

lemma sg3533 : RowSquare [8,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2707

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

lemma sg4287 : RowSquare [7,4,1,1,1,1,1] [5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg1188

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

lemma sg11207 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg1945

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

lemma sg14374 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2737

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

lemma sg15616 : RowSquare [7,6,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg6469

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

lemma sg18913 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6470

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18978 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4287

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19621 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg15616

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19834 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11207

lemma sg19835 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14374

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36483 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19834

lemma sg36494 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,6,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19835

lemma sg36500 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,6,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18978

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

lemma degreeTree62_404All_oai : degreeTree62_404.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36491,⟨sg36486,⟨sg36483,⟨sg36482,⟨sg36481,True.intro,True.intro⟩,True.intro⟩,⟨sg36485,⟨sg36484,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36489,⟨sg36488,⟨sg36487,True.intro,True.intro⟩,True.intro⟩,⟨sg36490,True.intro,True.intro⟩⟩⟩,⟨sg36497,⟨sg36494,⟨sg36493,⟨sg36492,True.intro,True.intro⟩,True.intro⟩,⟨sg36496,⟨sg36495,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36500,⟨sg36499,⟨sg36498,True.intro,True.intro⟩,True.intro⟩,⟨sg36501,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_404All_oai := @OAI.UniversalTensorSquare.degreeTree62_404All_oai
