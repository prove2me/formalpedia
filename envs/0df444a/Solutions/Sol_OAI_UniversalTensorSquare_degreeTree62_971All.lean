-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_971All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T21:44:02.891735+00:00
-- url     : https://prove2.me/submissions/94df997a-347b-48b7-af6b-c9304f793129

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg155
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17843
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg20170
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg20510
import Theorems.Thm_OAI_UniversalTensorSquare_sg23
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg42709
import Theorems.Thm_OAI_UniversalTensorSquare_sg42710
import Theorems.Thm_OAI_UniversalTensorSquare_sg42711
import Theorems.Thm_OAI_UniversalTensorSquare_sg42715
import Theorems.Thm_OAI_UniversalTensorSquare_sg42716
import Theorems.Thm_OAI_UniversalTensorSquare_sg42717
import Theorems.Thm_OAI_UniversalTensorSquare_sg42718
import Theorems.Thm_OAI_UniversalTensorSquare_sg42719
import Theorems.Thm_OAI_UniversalTensorSquare_sg42720
import Theorems.Thm_OAI_UniversalTensorSquare_sg42721
import Theorems.Thm_OAI_UniversalTensorSquare_sg42722
import Theorems.Thm_OAI_UniversalTensorSquare_sg42723
import Theorems.Thm_OAI_UniversalTensorSquare_sg42725
import Theorems.Thm_OAI_UniversalTensorSquare_sg42726
import Theorems.Thm_OAI_UniversalTensorSquare_sg42727
import Theorems.Thm_OAI_UniversalTensorSquare_sg42729
import Theorems.Thm_OAI_UniversalTensorSquare_sg65

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

lemma sg457 : RowSquare [3,2,1,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

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

lemma sg1233 : RowSquare [4,3,3,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg65

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

lemma sg1962 : RowSquare [8,2,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg372

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

lemma sg3508 : RowSquare [7,4,3,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1233

lemma sg3676 : RowSquare [9,2,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1329

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

lemma sg4118 : RowSquare [6,4,3,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg155 sg457

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13977 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1962 sg3508

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

lemma sg17841 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3676 sg4118

lemma sg17846 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13977

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 105. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42712 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,6,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17846

lemma sg42713 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,6,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20170

lemma sg42714 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,6,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20170

lemma sg42724 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,6,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17841

lemma sg42728 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,13,7,6,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17843

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

lemma degreeTree62_971All_oai : degreeTree62_971.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42719,⟨sg42714,⟨sg42711,⟨sg42710,⟨sg42709,True.intro,True.intro⟩,True.intro⟩,⟨sg42713,⟨sg42712,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42717,⟨sg42716,⟨sg42715,True.intro,True.intro⟩,True.intro⟩,⟨sg42718,True.intro,True.intro⟩⟩⟩,⟨sg42725,⟨sg42722,⟨sg42721,⟨sg42720,True.intro,True.intro⟩,True.intro⟩,⟨sg42724,⟨sg42723,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42728,⟨sg42727,⟨sg42726,True.intro,True.intro⟩,True.intro⟩,⟨sg42729,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_971All_oai := @OAI.UniversalTensorSquare.degreeTree62_971All_oai
