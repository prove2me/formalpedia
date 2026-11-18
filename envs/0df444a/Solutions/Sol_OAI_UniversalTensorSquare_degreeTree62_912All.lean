-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_912All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:27:57.149344+00:00
-- url     : https://prove2.me/submissions/73117799-c4db-41f8-90c6-b044d1155eb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg16168
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1814
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg42074
import Theorems.Thm_OAI_UniversalTensorSquare_sg42076
import Theorems.Thm_OAI_UniversalTensorSquare_sg42077
import Theorems.Thm_OAI_UniversalTensorSquare_sg42078
import Theorems.Thm_OAI_UniversalTensorSquare_sg42079
import Theorems.Thm_OAI_UniversalTensorSquare_sg42080
import Theorems.Thm_OAI_UniversalTensorSquare_sg42081
import Theorems.Thm_OAI_UniversalTensorSquare_sg42082
import Theorems.Thm_OAI_UniversalTensorSquare_sg42083
import Theorems.Thm_OAI_UniversalTensorSquare_sg42084
import Theorems.Thm_OAI_UniversalTensorSquare_sg42085
import Theorems.Thm_OAI_UniversalTensorSquare_sg42087
import Theorems.Thm_OAI_UniversalTensorSquare_sg42088
import Theorems.Thm_OAI_UniversalTensorSquare_sg42089
import Theorems.Thm_OAI_UniversalTensorSquare_sg42091
import Theorems.Thm_OAI_UniversalTensorSquare_sg42092
import Theorems.Thm_OAI_UniversalTensorSquare_sg42093
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
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

lemma sg84 : RowSquare [3,3] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg13

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg241 : RowSquare [2,2,1,1,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg17

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg644 : RowSquare [5,3,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg32

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

lemma sg1498 : RowSquare [7,1,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg586

lemma sg1532 : RowSquare [7,2,2] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg87

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

lemma sg3103 : RowSquare [8,4,2] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg644

lemma sg3256 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg998

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

lemma sg4837 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1755

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

lemma sg3522 : RowSquare [8,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg430

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12343 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1532 sg3103

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

lemma sg11190 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1814

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

lemma sg15680 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3256

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17775 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg84 sg12343

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

lemma sg18844 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,8,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg241 sg11190

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20504 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4837

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

lemma sg20837 : RowSquare [10,8,2,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15680

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42073 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17775

lemma sg42075 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17775

lemma sg42086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,9,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20837 sg16168

lemma sg42090 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,5,5,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18844

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

lemma degreeTree62_912All_oai : degreeTree62_912.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42083,⟨sg42078,⟨sg42075,⟨sg42074,⟨sg42073,True.intro,True.intro⟩,True.intro⟩,⟨sg42077,⟨sg42076,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42081,⟨sg42080,⟨sg42079,True.intro,True.intro⟩,True.intro⟩,⟨sg42082,True.intro,True.intro⟩⟩⟩,⟨sg42089,⟨sg42086,⟨sg42085,⟨sg42084,True.intro,True.intro⟩,True.intro⟩,⟨sg42088,⟨sg42087,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42092,⟨sg42091,⟨sg42090,True.intro,True.intro⟩,True.intro⟩,⟨sg42093,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_912All_oai := @OAI.UniversalTensorSquare.degreeTree62_912All_oai
