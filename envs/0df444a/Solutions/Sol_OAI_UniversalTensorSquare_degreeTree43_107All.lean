-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_107All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:12.848582+00:00
-- url     : https://prove2.me/submissions/35c4b0a9-6529-4bfc-b684-f81985ec2350
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10244
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg25032
import Theorems.Thm_OAI_UniversalTensorSquare_sg25033
import Theorems.Thm_OAI_UniversalTensorSquare_sg25034
import Theorems.Thm_OAI_UniversalTensorSquare_sg25035
import Theorems.Thm_OAI_UniversalTensorSquare_sg25036
import Theorems.Thm_OAI_UniversalTensorSquare_sg25037
import Theorems.Thm_OAI_UniversalTensorSquare_sg25038
import Theorems.Thm_OAI_UniversalTensorSquare_sg25039
import Theorems.Thm_OAI_UniversalTensorSquare_sg25040
import Theorems.Thm_OAI_UniversalTensorSquare_sg25041
import Theorems.Thm_OAI_UniversalTensorSquare_sg25042
import Theorems.Thm_OAI_UniversalTensorSquare_sg25043
import Theorems.Thm_OAI_UniversalTensorSquare_sg25044
import Theorems.Thm_OAI_UniversalTensorSquare_sg25045
import Theorems.Thm_OAI_UniversalTensorSquare_sg25046
import Theorems.Thm_OAI_UniversalTensorSquare_sg25047
import Theorems.Thm_OAI_UniversalTensorSquare_sg25048
import Theorems.Thm_OAI_UniversalTensorSquare_sg25049
import Theorems.Thm_OAI_UniversalTensorSquare_sg25050
import Theorems.Thm_OAI_UniversalTensorSquare_sg25051
import Theorems.Thm_OAI_UniversalTensorSquare_sg25052
import Theorems.Thm_OAI_UniversalTensorSquare_sg25053
import Theorems.Thm_OAI_UniversalTensorSquare_sg25054
import Theorems.Thm_OAI_UniversalTensorSquare_sg25055
import Theorems.Thm_OAI_UniversalTensorSquare_sg25056
import Theorems.Thm_OAI_UniversalTensorSquare_sg25057
import Theorems.Thm_OAI_UniversalTensorSquare_sg25058
import Theorems.Thm_OAI_UniversalTensorSquare_sg25059
import Theorems.Thm_OAI_UniversalTensorSquare_sg25062
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg9518

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

lemma sg25060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9518

lemma sg25061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10244

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

lemma degreeTree43_107All_oai : degreeTree43_107.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25047,⟨sg25039,⟨sg25035,⟨sg25033,⟨sg25032,True.intro,True.intro⟩,⟨sg25034,True.intro,True.intro⟩⟩,⟨sg25037,⟨sg25036,True.intro,True.intro⟩,⟨sg25038,True.intro,True.intro⟩⟩⟩,⟨sg25043,⟨sg25041,⟨sg25040,True.intro,True.intro⟩,⟨sg25042,True.intro,True.intro⟩⟩,⟨sg25045,⟨sg25044,True.intro,True.intro⟩,⟨sg25046,True.intro,True.intro⟩⟩⟩⟩,⟨sg25055,⟨sg25051,⟨sg25049,⟨sg25048,True.intro,True.intro⟩,⟨sg25050,True.intro,True.intro⟩⟩,⟨sg25053,⟨sg25052,True.intro,True.intro⟩,⟨sg25054,True.intro,True.intro⟩⟩⟩,⟨sg25059,⟨sg25057,⟨sg25056,True.intro,True.intro⟩,⟨sg25058,True.intro,True.intro⟩⟩,⟨sg25061,⟨sg25060,True.intro,True.intro⟩,⟨sg25062,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_107All_oai := @OAI.UniversalTensorSquare.degreeTree43_107All_oai
