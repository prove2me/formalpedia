-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_544All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:58:07.884188+00:00
-- url     : https://prove2.me/submissions/320aaab3-84c2-4b7e-8ceb-3f3dd9b6c1f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_540All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_542All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg12691
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg30581
import Theorems.Thm_OAI_UniversalTensorSquare_sg30582
import Theorems.Thm_OAI_UniversalTensorSquare_sg30583
import Theorems.Thm_OAI_UniversalTensorSquare_sg30584
import Theorems.Thm_OAI_UniversalTensorSquare_sg30585
import Theorems.Thm_OAI_UniversalTensorSquare_sg30586
import Theorems.Thm_OAI_UniversalTensorSquare_sg30587
import Theorems.Thm_OAI_UniversalTensorSquare_sg30588
import Theorems.Thm_OAI_UniversalTensorSquare_sg30589
import Theorems.Thm_OAI_UniversalTensorSquare_sg30591
import Theorems.Thm_OAI_UniversalTensorSquare_sg30592
import Theorems.Thm_OAI_UniversalTensorSquare_sg30593
import Theorems.Thm_OAI_UniversalTensorSquare_sg30594
import Theorems.Thm_OAI_UniversalTensorSquare_sg30595
import Theorems.Thm_OAI_UniversalTensorSquare_sg30599
import Theorems.Thm_OAI_UniversalTensorSquare_sg30600
import Theorems.Thm_OAI_UniversalTensorSquare_sg30601
import Theorems.Thm_OAI_UniversalTensorSquare_sg30602
import Theorems.Thm_OAI_UniversalTensorSquare_sg30604
import Theorems.Thm_OAI_UniversalTensorSquare_sg30606
import Theorems.Thm_OAI_UniversalTensorSquare_sg30608
import Theorems.Thm_OAI_UniversalTensorSquare_sg30609
import Theorems.Thm_OAI_UniversalTensorSquare_sg30610
import Theorems.Thm_OAI_UniversalTensorSquare_sg30611
import Theorems.Thm_OAI_UniversalTensorSquare_sg30612
import Theorems.Thm_OAI_UniversalTensorSquare_sg30613
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg5261
import Theorems.Thm_OAI_UniversalTensorSquare_sg5757
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9626

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg124 : RowSquare [2,2,2,1] [3,2,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1077 : RowSquare [6,4] [4,3,3] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
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

lemma sg220 : RowSquare [5,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg676 : RowSquare [6,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

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

lemma sg739 : RowSquare [3,2,1,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg89

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

lemma sg1900 : RowSquare [7,2,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg68

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

lemma sg2205 : RowSquare [6,4,2,1] [5,4,4] := by
  exact rowSquare_join (by decide) sg97 sg124

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

lemma sg5144 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg676 sg676

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3168 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg220 sg390

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

lemma sg9065 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1900

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

lemma sg10384 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg5144

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

lemma sg8877 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14804 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg739 sg5757

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

lemma sg15563 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7812

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 75. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10384

lemma sg30596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9626

lemma sg30597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9626

lemma sg30598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2205 sg15563

lemma sg30603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5261 sg12691

lemma sg30605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8877 sg9065

lemma sg30607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3168 sg14804

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

lemma degreeTree43_541All : degreeTree43_541.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30597,⟨sg30589,⟨sg30585,⟨sg30583,⟨sg30582,True.intro,True.intro⟩,⟨sg30584,True.intro,True.intro⟩⟩,⟨sg30587,⟨sg30586,True.intro,True.intro⟩,⟨sg30588,True.intro,True.intro⟩⟩⟩,⟨sg30593,⟨sg30591,⟨sg30590,True.intro,True.intro⟩,⟨sg30592,True.intro,True.intro⟩⟩,⟨sg30595,⟨sg30594,True.intro,True.intro⟩,⟨sg30596,True.intro,True.intro⟩⟩⟩⟩,⟨sg30605,⟨sg30601,⟨sg30599,⟨sg30598,True.intro,True.intro⟩,⟨sg30600,True.intro,True.intro⟩⟩,⟨sg30603,⟨sg30602,True.intro,True.intro⟩,⟨sg30604,True.intro,True.intro⟩⟩⟩,⟨sg30609,⟨sg30607,⟨sg30606,True.intro,True.intro⟩,⟨sg30608,True.intro,True.intro⟩⟩,⟨sg30611,⟨sg30610,True.intro,True.intro⟩,⟨sg30612,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_543All : degreeTree43_543.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30613,degreeTree43_541All,degreeTree43_542All⟩

lemma degreeTree43_544All_oai : degreeTree43_544.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30581,degreeTree43_540All,degreeTree43_543All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_544All_oai := @OAI.UniversalTensorSquare.degreeTree43_544All_oai
