-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_368All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:51:02.11121+00:00
-- url     : https://prove2.me/submissions/6a8fd7fa-c4c2-4dff-aedb-d7f5b4f50972
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_366All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10334
import Theorems.Thm_OAI_UniversalTensorSquare_sg113
import Theorems.Thm_OAI_UniversalTensorSquare_sg12
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg28342
import Theorems.Thm_OAI_UniversalTensorSquare_sg28344
import Theorems.Thm_OAI_UniversalTensorSquare_sg28345
import Theorems.Thm_OAI_UniversalTensorSquare_sg28347
import Theorems.Thm_OAI_UniversalTensorSquare_sg28348
import Theorems.Thm_OAI_UniversalTensorSquare_sg28349
import Theorems.Thm_OAI_UniversalTensorSquare_sg28350
import Theorems.Thm_OAI_UniversalTensorSquare_sg28351
import Theorems.Thm_OAI_UniversalTensorSquare_sg28352
import Theorems.Thm_OAI_UniversalTensorSquare_sg28353
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg587
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9473
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

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

lemma sg205 : RowSquare [4,2,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg12

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

lemma sg708 : RowSquare [7,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg32

lemma sg818 : RowSquare [4,2,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg178

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

lemma sg1037 : RowSquare [6,2,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

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

lemma sg1383 : RowSquare [6,2,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg537

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

lemma sg2627 : RowSquare [6,3,2,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg205 sg113

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

lemma sg5313 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg708

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

lemma sg6349 : RowSquare [6,4,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1754

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

lemma sg6747 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1037

lemma sg6925 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1005

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

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

lemma sg8417 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2627

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

lemma sg9235 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1383

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

lemma sg10333 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6925

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

lemma sg9889 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6747

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

lemma sg8750 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg818 sg1327

lemma sg8796 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6349

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

lemma sg10752 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5313

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10333

lemma sg28340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9235

lemma sg28341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8750 sg9473

lemma sg28343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10752

lemma sg28346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9889

lemma sg28354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10334

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

lemma degreeTree43_367All : degreeTree43_367.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28347,⟨sg28343,⟨sg28341,⟨sg28340,True.intro,True.intro⟩,⟨sg28342,True.intro,True.intro⟩⟩,⟨sg28345,⟨sg28344,True.intro,True.intro⟩,⟨sg28346,True.intro,True.intro⟩⟩⟩,⟨sg28351,⟨sg28349,⟨sg28348,True.intro,True.intro⟩,⟨sg28350,True.intro,True.intro⟩⟩,⟨sg28353,⟨sg28352,True.intro,True.intro⟩,⟨sg28354,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_368All_oai : degreeTree43_368.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28339,degreeTree43_366All,degreeTree43_367All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_368All_oai := @OAI.UniversalTensorSquare.degreeTree43_368All_oai
