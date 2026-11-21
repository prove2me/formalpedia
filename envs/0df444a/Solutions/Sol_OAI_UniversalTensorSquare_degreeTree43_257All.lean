-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_257All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:33.879914+00:00
-- url     : https://prove2.me/submissions/83e9ec83-9835-4f67-95ee-427d4c61acd5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_253All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_256All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1379
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg26919
import Theorems.Thm_OAI_UniversalTensorSquare_sg26920
import Theorems.Thm_OAI_UniversalTensorSquare_sg26923
import Theorems.Thm_OAI_UniversalTensorSquare_sg26924
import Theorems.Thm_OAI_UniversalTensorSquare_sg26926
import Theorems.Thm_OAI_UniversalTensorSquare_sg26927
import Theorems.Thm_OAI_UniversalTensorSquare_sg26928
import Theorems.Thm_OAI_UniversalTensorSquare_sg26930
import Theorems.Thm_OAI_UniversalTensorSquare_sg26932
import Theorems.Thm_OAI_UniversalTensorSquare_sg26933
import Theorems.Thm_OAI_UniversalTensorSquare_sg26934
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg891
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9222
import Theorems.Thm_OAI_UniversalTensorSquare_sg9223
import Theorems.Thm_OAI_UniversalTensorSquare_sg9841
import Theorems.Thm_OAI_UniversalTensorSquare_sg9842
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

lemma sg7788 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg891

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

lemma sg8265 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1005 sg1379

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

lemma sg9224 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1782

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

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

lemma sg8813 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7788

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

lemma sg10845 : RowSquare [7,5,2,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2702

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9222

lemma sg26922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9841

lemma sg26925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9223

lemma sg26929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8265 sg10845

lemma sg26931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9224

lemma sg26935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9842

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

lemma degreeTree43_254All : degreeTree43_254.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26927,⟨sg26923,⟨sg26921,⟨sg26920,True.intro,True.intro⟩,⟨sg26922,True.intro,True.intro⟩⟩,⟨sg26925,⟨sg26924,True.intro,True.intro⟩,⟨sg26926,True.intro,True.intro⟩⟩⟩,⟨sg26931,⟨sg26929,⟨sg26928,True.intro,True.intro⟩,⟨sg26930,True.intro,True.intro⟩⟩,⟨sg26933,⟨sg26932,True.intro,True.intro⟩,⟨sg26934,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_255All : degreeTree43_255.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26919,degreeTree43_253All,degreeTree43_254All⟩

lemma degreeTree43_257All_oai : degreeTree43_257.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26935,degreeTree43_255All,degreeTree43_256All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_257All_oai := @OAI.UniversalTensorSquare.degreeTree43_257All_oai
