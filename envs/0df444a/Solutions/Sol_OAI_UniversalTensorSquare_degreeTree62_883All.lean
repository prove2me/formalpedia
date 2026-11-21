-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_883All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T20:32:18.416858+00:00
-- url     : https://prove2.me/submissions/e032af98-8e2c-4ad3-8586-4942819e2ca3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg356
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg41766
import Theorems.Thm_OAI_UniversalTensorSquare_sg41767
import Theorems.Thm_OAI_UniversalTensorSquare_sg41768
import Theorems.Thm_OAI_UniversalTensorSquare_sg41769
import Theorems.Thm_OAI_UniversalTensorSquare_sg41771
import Theorems.Thm_OAI_UniversalTensorSquare_sg41773
import Theorems.Thm_OAI_UniversalTensorSquare_sg41774
import Theorems.Thm_OAI_UniversalTensorSquare_sg41775
import Theorems.Thm_OAI_UniversalTensorSquare_sg41776
import Theorems.Thm_OAI_UniversalTensorSquare_sg41777
import Theorems.Thm_OAI_UniversalTensorSquare_sg41781
import Theorems.Thm_OAI_UniversalTensorSquare_sg41782
import Theorems.Thm_OAI_UniversalTensorSquare_sg41783
import Theorems.Thm_OAI_UniversalTensorSquare_sg41784
import Theorems.Thm_OAI_UniversalTensorSquare_sg41786
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg703

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

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
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

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg364 : RowSquare [4,4] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

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

lemma sg1069 : RowSquare [6,3,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

lemma sg1095 : RowSquare [7,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg373

lemma sg1105 : RowSquare [7,2,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg390

lemma sg1206 : RowSquare [4,3,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg178

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

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

lemma sg1588 : RowSquare [3,2,2,2,2,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg356

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

lemma sg2004 : RowSquare [9,2,1] [6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg105

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

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

lemma sg5827 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1095

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

lemma sg6534 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1069 sg1105

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

lemma sg11112 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2004

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

lemma sg18822 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg1206 sg6534

lemma sg18823 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,7,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1588 sg5827

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

lemma sg20094 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11112

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

lemma sg20314 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg5737

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

lemma sg41770 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18822

lemma sg41772 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18823

lemma sg41778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20094

lemma sg41779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18822

lemma sg41780 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20094

lemma sg41785 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18823

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

lemma degreeTree62_883All_oai : degreeTree62_883.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41776,⟨sg41771,⟨sg41768,⟨sg41767,⟨sg41766,True.intro,True.intro⟩,True.intro⟩,⟨sg41770,⟨sg41769,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41774,⟨sg41773,⟨sg41772,True.intro,True.intro⟩,True.intro⟩,⟨sg41775,True.intro,True.intro⟩⟩⟩,⟨sg41782,⟨sg41779,⟨sg41778,⟨sg41777,True.intro,True.intro⟩,True.intro⟩,⟨sg41781,⟨sg41780,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41785,⟨sg41784,⟨sg41783,True.intro,True.intro⟩,True.intro⟩,⟨sg41786,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_883All_oai := @OAI.UniversalTensorSquare.degreeTree62_883All_oai
