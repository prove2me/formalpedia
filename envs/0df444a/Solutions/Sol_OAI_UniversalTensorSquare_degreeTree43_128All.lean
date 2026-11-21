-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_128All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:21.342589+00:00
-- url     : https://prove2.me/submissions/6805c5e5-c302-485c-9a73-44507c647a00

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25322
import Theorems.Thm_OAI_UniversalTensorSquare_sg25323
import Theorems.Thm_OAI_UniversalTensorSquare_sg25324
import Theorems.Thm_OAI_UniversalTensorSquare_sg25325
import Theorems.Thm_OAI_UniversalTensorSquare_sg25326
import Theorems.Thm_OAI_UniversalTensorSquare_sg25327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25329
import Theorems.Thm_OAI_UniversalTensorSquare_sg25330
import Theorems.Thm_OAI_UniversalTensorSquare_sg25331
import Theorems.Thm_OAI_UniversalTensorSquare_sg25332
import Theorems.Thm_OAI_UniversalTensorSquare_sg25333
import Theorems.Thm_OAI_UniversalTensorSquare_sg25334
import Theorems.Thm_OAI_UniversalTensorSquare_sg25335
import Theorems.Thm_OAI_UniversalTensorSquare_sg25336
import Theorems.Thm_OAI_UniversalTensorSquare_sg25337
import Theorems.Thm_OAI_UniversalTensorSquare_sg25339
import Theorems.Thm_OAI_UniversalTensorSquare_sg25340
import Theorems.Thm_OAI_UniversalTensorSquare_sg25341
import Theorems.Thm_OAI_UniversalTensorSquare_sg25342
import Theorems.Thm_OAI_UniversalTensorSquare_sg25343
import Theorems.Thm_OAI_UniversalTensorSquare_sg25345
import Theorems.Thm_OAI_UniversalTensorSquare_sg25347
import Theorems.Thm_OAI_UniversalTensorSquare_sg25348
import Theorems.Thm_OAI_UniversalTensorSquare_sg25350
import Theorems.Thm_OAI_UniversalTensorSquare_sg25351
import Theorems.Thm_OAI_UniversalTensorSquare_sg25352
import Theorems.Thm_OAI_UniversalTensorSquare_sg314
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg5422
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8559
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9529
import Theorems.Thm_OAI_UniversalTensorSquare_sg9530

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

lemma sg1674 : RowSquare [5,2,2,1,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg314

lemma sg1908 : RowSquare [7,3,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg373

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5421 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg910

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

lemma sg8189 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1908

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

lemma sg10093 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1674

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

lemma sg10857 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5421

lemma sg10858 : RowSquare [7,6,2,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5422

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10093

lemma sg25338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8189 sg10857

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9529

lemma sg25346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8189 sg10858

lemma sg25349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9530

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

lemma degreeTree43_128All_oai : degreeTree43_128.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25337,⟨sg25329,⟨sg25325,⟨sg25323,⟨sg25322,True.intro,True.intro⟩,⟨sg25324,True.intro,True.intro⟩⟩,⟨sg25327,⟨sg25326,True.intro,True.intro⟩,⟨sg25328,True.intro,True.intro⟩⟩⟩,⟨sg25333,⟨sg25331,⟨sg25330,True.intro,True.intro⟩,⟨sg25332,True.intro,True.intro⟩⟩,⟨sg25335,⟨sg25334,True.intro,True.intro⟩,⟨sg25336,True.intro,True.intro⟩⟩⟩⟩,⟨sg25345,⟨sg25341,⟨sg25339,⟨sg25338,True.intro,True.intro⟩,⟨sg25340,True.intro,True.intro⟩⟩,⟨sg25343,⟨sg25342,True.intro,True.intro⟩,⟨sg25344,True.intro,True.intro⟩⟩⟩,⟨sg25349,⟨sg25347,⟨sg25346,True.intro,True.intro⟩,⟨sg25348,True.intro,True.intro⟩⟩,⟨sg25351,⟨sg25350,True.intro,True.intro⟩,⟨sg25352,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_128All_oai := @OAI.UniversalTensorSquare.degreeTree43_128All_oai
