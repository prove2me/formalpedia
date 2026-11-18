-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_32All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:11.26676+00:00
-- url     : https://prove2.me/submissions/526c8e99-fcf3-4d7f-882b-0eb7b1f5c481
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg1023
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg13511
import Theorems.Thm_OAI_UniversalTensorSquare_sg16674
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg32379
import Theorems.Thm_OAI_UniversalTensorSquare_sg32380
import Theorems.Thm_OAI_UniversalTensorSquare_sg32381
import Theorems.Thm_OAI_UniversalTensorSquare_sg32382
import Theorems.Thm_OAI_UniversalTensorSquare_sg32383
import Theorems.Thm_OAI_UniversalTensorSquare_sg32385
import Theorems.Thm_OAI_UniversalTensorSquare_sg32386
import Theorems.Thm_OAI_UniversalTensorSquare_sg32387
import Theorems.Thm_OAI_UniversalTensorSquare_sg32388
import Theorems.Thm_OAI_UniversalTensorSquare_sg32389
import Theorems.Thm_OAI_UniversalTensorSquare_sg32390
import Theorems.Thm_OAI_UniversalTensorSquare_sg32391
import Theorems.Thm_OAI_UniversalTensorSquare_sg32392
import Theorems.Thm_OAI_UniversalTensorSquare_sg32394
import Theorems.Thm_OAI_UniversalTensorSquare_sg32396
import Theorems.Thm_OAI_UniversalTensorSquare_sg32398
import Theorems.Thm_OAI_UniversalTensorSquare_sg4488
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg975

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

lemma sg18 : RowSquare [3,1] [3,1] := by
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

lemma sg244 : RowSquare [2,2,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg17 sg18

lemma sg441 : RowSquare [2,2,2,1,1,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg40

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

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

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

lemma sg2114 : RowSquare [5,1,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg7 sg1023

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

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

lemma sg2632 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg92 sg244

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

lemma sg4933 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2114

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

lemma sg3332 : RowSquare [6,3,3,1,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg89 sg441

lemma sg3656 : RowSquare [8,4,3] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg975

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

lemma sg13510 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1891 sg3656

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

lemma sg14470 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2632

lemma sg14471 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2633

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16249 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13510

lemma sg16250 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13511

lemma sg16251 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg3332 sg4488

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20636 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4933

lemma sg20699 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14470

lemma sg20700 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14471

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32384 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16249

lemma sg32393 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16250

lemma sg32395 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16674

lemma sg32397 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16251

lemma sg32399 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16251

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

lemma degreeTree62_32All_oai : degreeTree62_32.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32389,⟨sg32384,⟨sg32381,⟨sg32380,⟨sg32379,True.intro,True.intro⟩,True.intro⟩,⟨sg32383,⟨sg32382,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32387,⟨sg32386,⟨sg32385,True.intro,True.intro⟩,True.intro⟩,⟨sg32388,True.intro,True.intro⟩⟩⟩,⟨sg32395,⟨sg32392,⟨sg32391,⟨sg32390,True.intro,True.intro⟩,True.intro⟩,⟨sg32394,⟨sg32393,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32398,⟨sg32397,⟨sg32396,True.intro,True.intro⟩,True.intro⟩,⟨sg32399,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_32All_oai := @OAI.UniversalTensorSquare.degreeTree62_32All_oai
