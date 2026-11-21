-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_408All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:07:07.975686+00:00
-- url     : https://prove2.me/submissions/e36885f1-a822-46a5-9c33-efdcf7143406

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17373
import Theorems.Thm_OAI_UniversalTensorSquare_sg18433
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg36547
import Theorems.Thm_OAI_UniversalTensorSquare_sg36549
import Theorems.Thm_OAI_UniversalTensorSquare_sg36550
import Theorems.Thm_OAI_UniversalTensorSquare_sg36552
import Theorems.Thm_OAI_UniversalTensorSquare_sg36554
import Theorems.Thm_OAI_UniversalTensorSquare_sg36555
import Theorems.Thm_OAI_UniversalTensorSquare_sg36556
import Theorems.Thm_OAI_UniversalTensorSquare_sg36557
import Theorems.Thm_OAI_UniversalTensorSquare_sg36558
import Theorems.Thm_OAI_UniversalTensorSquare_sg36559
import Theorems.Thm_OAI_UniversalTensorSquare_sg36560
import Theorems.Thm_OAI_UniversalTensorSquare_sg36561
import Theorems.Thm_OAI_UniversalTensorSquare_sg36562
import Theorems.Thm_OAI_UniversalTensorSquare_sg36563
import Theorems.Thm_OAI_UniversalTensorSquare_sg36564
import Theorems.Thm_OAI_UniversalTensorSquare_sg36566
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

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

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

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

lemma sg1625 : RowSquare [4,2,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg383

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

lemma sg5741 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg1625

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

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

lemma sg20318 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5741

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 90. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36548 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18433

lemma sg36551 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18433

lemma sg36553 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18433

lemma sg36565 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17373

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

lemma degreeTree62_408All_oai : degreeTree62_408.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36557,⟨sg36552,⟨sg36549,⟨sg36548,⟨sg36547,True.intro,True.intro⟩,True.intro⟩,⟨sg36551,⟨sg36550,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36555,⟨sg36554,⟨sg36553,True.intro,True.intro⟩,True.intro⟩,⟨sg36556,True.intro,True.intro⟩⟩⟩,⟨sg36562,⟨sg36560,⟨sg36559,⟨sg36558,True.intro,True.intro⟩,True.intro⟩,⟨sg36561,True.intro,True.intro⟩⟩,⟨sg36565,⟨sg36564,⟨sg36563,True.intro,True.intro⟩,True.intro⟩,⟨sg36566,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_408All_oai := @OAI.UniversalTensorSquare.degreeTree62_408All_oai
