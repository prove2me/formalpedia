-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_75All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:48:57.642012+00:00
-- url     : https://prove2.me/submissions/57b685ec-8296-43f8-9e68-18a4a61d0ca8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10236
import Theorems.Thm_OAI_UniversalTensorSquare_sg10243
import Theorems.Thm_OAI_UniversalTensorSquare_sg10244
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg1338
import Theorems.Thm_OAI_UniversalTensorSquare_sg1687
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg180
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg24676
import Theorems.Thm_OAI_UniversalTensorSquare_sg24677
import Theorems.Thm_OAI_UniversalTensorSquare_sg24679
import Theorems.Thm_OAI_UniversalTensorSquare_sg24680
import Theorems.Thm_OAI_UniversalTensorSquare_sg24681
import Theorems.Thm_OAI_UniversalTensorSquare_sg24682
import Theorems.Thm_OAI_UniversalTensorSquare_sg24683
import Theorems.Thm_OAI_UniversalTensorSquare_sg24684
import Theorems.Thm_OAI_UniversalTensorSquare_sg24685
import Theorems.Thm_OAI_UniversalTensorSquare_sg24686
import Theorems.Thm_OAI_UniversalTensorSquare_sg24688
import Theorems.Thm_OAI_UniversalTensorSquare_sg24689
import Theorems.Thm_OAI_UniversalTensorSquare_sg24690
import Theorems.Thm_OAI_UniversalTensorSquare_sg24691
import Theorems.Thm_OAI_UniversalTensorSquare_sg24692
import Theorems.Thm_OAI_UniversalTensorSquare_sg24693
import Theorems.Thm_OAI_UniversalTensorSquare_sg24695
import Theorems.Thm_OAI_UniversalTensorSquare_sg24696
import Theorems.Thm_OAI_UniversalTensorSquare_sg24697
import Theorems.Thm_OAI_UniversalTensorSquare_sg24699
import Theorems.Thm_OAI_UniversalTensorSquare_sg24700
import Theorems.Thm_OAI_UniversalTensorSquare_sg24701
import Theorems.Thm_OAI_UniversalTensorSquare_sg24705
import Theorems.Thm_OAI_UniversalTensorSquare_sg24706
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg551
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg595
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721
import Theorems.Thm_OAI_UniversalTensorSquare_sg9738

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

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

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

lemma sg8378 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1687

lemma sg8420 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg2626

lemma sg8426 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg551 sg1754

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

lemma sg10237 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1338

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

lemma sg10602 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2251

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

lemma sg9505 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1338

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

lemma sg24678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8426 sg10236

lemma sg24687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10243

lemma sg24694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9505

lemma sg24698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10237

lemma sg24702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10244

lemma sg24703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8378 sg10602

lemma sg24704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9738

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

lemma degreeTree43_75All_oai : degreeTree43_75.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24691,⟨sg24683,⟨sg24679,⟨sg24677,⟨sg24676,True.intro,True.intro⟩,⟨sg24678,True.intro,True.intro⟩⟩,⟨sg24681,⟨sg24680,True.intro,True.intro⟩,⟨sg24682,True.intro,True.intro⟩⟩⟩,⟨sg24687,⟨sg24685,⟨sg24684,True.intro,True.intro⟩,⟨sg24686,True.intro,True.intro⟩⟩,⟨sg24689,⟨sg24688,True.intro,True.intro⟩,⟨sg24690,True.intro,True.intro⟩⟩⟩⟩,⟨sg24699,⟨sg24695,⟨sg24693,⟨sg24692,True.intro,True.intro⟩,⟨sg24694,True.intro,True.intro⟩⟩,⟨sg24697,⟨sg24696,True.intro,True.intro⟩,⟨sg24698,True.intro,True.intro⟩⟩⟩,⟨sg24703,⟨sg24701,⟨sg24700,True.intro,True.intro⟩,⟨sg24702,True.intro,True.intro⟩⟩,⟨sg24705,⟨sg24704,True.intro,True.intro⟩,⟨sg24706,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_75All_oai := @OAI.UniversalTensorSquare.degreeTree43_75All_oai
