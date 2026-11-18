-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_617All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:21:48.557197+00:00
-- url     : https://prove2.me/submissions/4d01e6b6-93b0-4a1d-ba5d-5d8b1d884b98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_615All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg2380
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg358
import Theorems.Thm_OAI_UniversalTensorSquare_sg38826
import Theorems.Thm_OAI_UniversalTensorSquare_sg38829
import Theorems.Thm_OAI_UniversalTensorSquare_sg38832
import Theorems.Thm_OAI_UniversalTensorSquare_sg38834
import Theorems.Thm_OAI_UniversalTensorSquare_sg38835
import Theorems.Thm_OAI_UniversalTensorSquare_sg38836
import Theorems.Thm_OAI_UniversalTensorSquare_sg38837
import Theorems.Thm_OAI_UniversalTensorSquare_sg38838
import Theorems.Thm_OAI_UniversalTensorSquare_sg38839
import Theorems.Thm_OAI_UniversalTensorSquare_sg38840
import Theorems.Thm_OAI_UniversalTensorSquare_sg38842
import Theorems.Thm_OAI_UniversalTensorSquare_sg38845
import Theorems.Thm_OAI_UniversalTensorSquare_sg38846
import Theorems.Thm_OAI_UniversalTensorSquare_sg38847
import Theorems.Thm_OAI_UniversalTensorSquare_sg44
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg26 : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg429 : RowSquare [2,1,1,1,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg17 sg49

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg729 : RowSquare [2,2,2,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg44

lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg92

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

lemma sg2281 : RowSquare [7,2,2,1,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg313

lemma sg2297 : RowSquare [7,3,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg590

lemma sg2300 : RowSquare [7,3,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg312

lemma sg2344 : RowSquare [7,4,2] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg358

lemma sg2390 : RowSquare [8,2,2,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

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

lemma sg2962 : RowSquare [8,3,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg1001

lemma sg2971 : RowSquare [8,3,1,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg590

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

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

lemma sg6468 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg729

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

lemma sg3523 : RowSquare [8,1,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg429

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

lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg748

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

lemma sg12781 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2344

lemma sg12899 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,3] := by
  exact rowSquare_join (by decide) sg2380 sg2297

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

lemma sg14168 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2300 sg2962

lemma sg14292 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2281 sg2971

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

lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4167

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16834 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12781

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

lemma sg18909 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6468

lemma sg18911 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg6469

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

lemma sg19031 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14168

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

lemma sg19392 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14292

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

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

lemma sg19960 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12899

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

lemma sg20633 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3964

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19960

lemma sg38828 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19960

lemma sg38830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19960

lemma sg38831 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19960

lemma sg38833 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19960

lemma sg38841 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19392

lemma sg38843 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19031

lemma sg38844 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16834

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

lemma degreeTree62_616All : degreeTree62_616.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38837,⟨sg38832,⟨sg38829,⟨sg38828,⟨sg38827,True.intro,True.intro⟩,True.intro⟩,⟨sg38831,⟨sg38830,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38835,⟨sg38834,⟨sg38833,True.intro,True.intro⟩,True.intro⟩,⟨sg38836,True.intro,True.intro⟩⟩⟩,⟨sg38843,⟨sg38840,⟨sg38839,⟨sg38838,True.intro,True.intro⟩,True.intro⟩,⟨sg38842,⟨sg38841,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38846,⟨sg38845,⟨sg38844,True.intro,True.intro⟩,True.intro⟩,⟨sg38847,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_617All_oai : degreeTree62_617.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38826,degreeTree62_615All,degreeTree62_616All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_617All_oai := @OAI.UniversalTensorSquare.degreeTree62_617All_oai
