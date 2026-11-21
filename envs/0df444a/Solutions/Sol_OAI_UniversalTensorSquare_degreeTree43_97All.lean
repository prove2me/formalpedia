-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_97All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:58.799772+00:00
-- url     : https://prove2.me/submissions/e66869e3-259e-4c31-be72-b5e03f1fd127

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1039
import Theorems.Thm_OAI_UniversalTensorSquare_sg12686
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg24903
import Theorems.Thm_OAI_UniversalTensorSquare_sg24904
import Theorems.Thm_OAI_UniversalTensorSquare_sg24905
import Theorems.Thm_OAI_UniversalTensorSquare_sg24907
import Theorems.Thm_OAI_UniversalTensorSquare_sg24908
import Theorems.Thm_OAI_UniversalTensorSquare_sg24910
import Theorems.Thm_OAI_UniversalTensorSquare_sg24911
import Theorems.Thm_OAI_UniversalTensorSquare_sg24913
import Theorems.Thm_OAI_UniversalTensorSquare_sg24914
import Theorems.Thm_OAI_UniversalTensorSquare_sg24917
import Theorems.Thm_OAI_UniversalTensorSquare_sg24918
import Theorems.Thm_OAI_UniversalTensorSquare_sg24919
import Theorems.Thm_OAI_UniversalTensorSquare_sg24920
import Theorems.Thm_OAI_UniversalTensorSquare_sg24921
import Theorems.Thm_OAI_UniversalTensorSquare_sg24922
import Theorems.Thm_OAI_UniversalTensorSquare_sg24923
import Theorems.Thm_OAI_UniversalTensorSquare_sg24924
import Theorems.Thm_OAI_UniversalTensorSquare_sg24927
import Theorems.Thm_OAI_UniversalTensorSquare_sg24928
import Theorems.Thm_OAI_UniversalTensorSquare_sg24929
import Theorems.Thm_OAI_UniversalTensorSquare_sg24930
import Theorems.Thm_OAI_UniversalTensorSquare_sg24931
import Theorems.Thm_OAI_UniversalTensorSquare_sg24932
import Theorems.Thm_OAI_UniversalTensorSquare_sg24933
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg378
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9510
import Theorems.Thm_OAI_UniversalTensorSquare_sg961
import Theorems.Thm_OAI_UniversalTensorSquare_sg9748
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

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

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

lemma sg1329 : RowSquare [6,1,1,1,1,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg111

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

lemma sg1339 : RowSquare [6,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg525

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

lemma sg1894 : RowSquare [7,2,2,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg178

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

lemma sg5255 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg961

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

lemma sg4744 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg999

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

lemma sg8989 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1894

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

lemma sg10241 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1339

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8741 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1329

lemma sg8745 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1330

lemma sg8869 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg4744

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

lemma sg9451 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1039 sg1754

lemma sg9458 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1330

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

lemma sg24906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10241

lemma sg24909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8869 sg8989

lemma sg24912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5255 sg12686

lemma sg24915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8745 sg9451

lemma sg24916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9510

lemma sg24925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8741 sg9458

lemma sg24926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9748

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

lemma degreeTree43_97All_oai : degreeTree43_97.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24918,⟨sg24910,⟨sg24906,⟨sg24904,⟨sg24903,True.intro,True.intro⟩,⟨sg24905,True.intro,True.intro⟩⟩,⟨sg24908,⟨sg24907,True.intro,True.intro⟩,⟨sg24909,True.intro,True.intro⟩⟩⟩,⟨sg24914,⟨sg24912,⟨sg24911,True.intro,True.intro⟩,⟨sg24913,True.intro,True.intro⟩⟩,⟨sg24916,⟨sg24915,True.intro,True.intro⟩,⟨sg24917,True.intro,True.intro⟩⟩⟩⟩,⟨sg24926,⟨sg24922,⟨sg24920,⟨sg24919,True.intro,True.intro⟩,⟨sg24921,True.intro,True.intro⟩⟩,⟨sg24924,⟨sg24923,True.intro,True.intro⟩,⟨sg24925,True.intro,True.intro⟩⟩⟩,⟨sg24930,⟨sg24928,⟨sg24927,True.intro,True.intro⟩,⟨sg24929,True.intro,True.intro⟩⟩,⟨sg24932,⟨sg24931,True.intro,True.intro⟩,⟨sg24933,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_97All_oai := @OAI.UniversalTensorSquare.degreeTree43_97All_oai
