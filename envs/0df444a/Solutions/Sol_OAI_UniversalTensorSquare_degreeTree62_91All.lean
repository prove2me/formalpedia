-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_91All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:28:09.970629+00:00
-- url     : https://prove2.me/submissions/37fbe978-046b-4e14-bbbb-fb776d9e6833
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_87All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_89All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17277
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg20531
import Theorems.Thm_OAI_UniversalTensorSquare_sg20640
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33015
import Theorems.Thm_OAI_UniversalTensorSquare_sg33016
import Theorems.Thm_OAI_UniversalTensorSquare_sg33017
import Theorems.Thm_OAI_UniversalTensorSquare_sg33018
import Theorems.Thm_OAI_UniversalTensorSquare_sg33019
import Theorems.Thm_OAI_UniversalTensorSquare_sg33021
import Theorems.Thm_OAI_UniversalTensorSquare_sg33023
import Theorems.Thm_OAI_UniversalTensorSquare_sg33024
import Theorems.Thm_OAI_UniversalTensorSquare_sg33025
import Theorems.Thm_OAI_UniversalTensorSquare_sg33027
import Theorems.Thm_OAI_UniversalTensorSquare_sg33028
import Theorems.Thm_OAI_UniversalTensorSquare_sg33030
import Theorems.Thm_OAI_UniversalTensorSquare_sg33032
import Theorems.Thm_OAI_UniversalTensorSquare_sg33033
import Theorems.Thm_OAI_UniversalTensorSquare_sg33034
import Theorems.Thm_OAI_UniversalTensorSquare_sg33035
import Theorems.Thm_OAI_UniversalTensorSquare_sg33036
import Theorems.Thm_OAI_UniversalTensorSquare_sg33037
import Theorems.Thm_OAI_UniversalTensorSquare_sg961

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

lemma sg1632 : RowSquare [4,3,1,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

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

lemma sg3655 : RowSquare [8,4,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg961

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

lemma sg4157 : RowSquare [7,2,2,2,2,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1632

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

lemma sg13671 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3655

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

lemma sg16688 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg3655 sg4157

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17211 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13671

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33020 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17277

lemma sg33022 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17277

lemma sg33026 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17277

lemma sg33029 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16688

lemma sg33031 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17211

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

lemma degreeTree62_88All : degreeTree62_88.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33026,⟨sg33021,⟨sg33018,⟨sg33017,⟨sg33016,True.intro,True.intro⟩,True.intro⟩,⟨sg33020,⟨sg33019,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33024,⟨sg33023,⟨sg33022,True.intro,True.intro⟩,True.intro⟩,⟨sg33025,True.intro,True.intro⟩⟩⟩,⟨sg33032,⟨sg33029,⟨sg33028,⟨sg33027,True.intro,True.intro⟩,True.intro⟩,⟨sg33031,⟨sg33030,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33035,⟨sg33034,⟨sg33033,True.intro,True.intro⟩,True.intro⟩,⟨sg33036,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_90All : degreeTree62_90.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33037,degreeTree62_88All,degreeTree62_89All⟩

lemma degreeTree62_91All_oai : degreeTree62_91.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33015,degreeTree62_87All,degreeTree62_90All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_91All_oai := @OAI.UniversalTensorSquare.degreeTree62_91All_oai
