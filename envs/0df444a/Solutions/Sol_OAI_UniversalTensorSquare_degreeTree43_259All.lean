-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_259All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:38.167135+00:00
-- url     : https://prove2.me/submissions/18aa21d8-21c9-4338-9d6b-20eff997f052

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1814
import Theorems.Thm_OAI_UniversalTensorSquare_sg18245
import Theorems.Thm_OAI_UniversalTensorSquare_sg27000
import Theorems.Thm_OAI_UniversalTensorSquare_sg27001
import Theorems.Thm_OAI_UniversalTensorSquare_sg27002
import Theorems.Thm_OAI_UniversalTensorSquare_sg27003
import Theorems.Thm_OAI_UniversalTensorSquare_sg27004
import Theorems.Thm_OAI_UniversalTensorSquare_sg27005
import Theorems.Thm_OAI_UniversalTensorSquare_sg27006
import Theorems.Thm_OAI_UniversalTensorSquare_sg27007
import Theorems.Thm_OAI_UniversalTensorSquare_sg27008
import Theorems.Thm_OAI_UniversalTensorSquare_sg27009
import Theorems.Thm_OAI_UniversalTensorSquare_sg27010
import Theorems.Thm_OAI_UniversalTensorSquare_sg27011
import Theorems.Thm_OAI_UniversalTensorSquare_sg27012
import Theorems.Thm_OAI_UniversalTensorSquare_sg27013
import Theorems.Thm_OAI_UniversalTensorSquare_sg27014
import Theorems.Thm_OAI_UniversalTensorSquare_sg27015
import Theorems.Thm_OAI_UniversalTensorSquare_sg27016
import Theorems.Thm_OAI_UniversalTensorSquare_sg27017
import Theorems.Thm_OAI_UniversalTensorSquare_sg27018
import Theorems.Thm_OAI_UniversalTensorSquare_sg27019
import Theorems.Thm_OAI_UniversalTensorSquare_sg27020
import Theorems.Thm_OAI_UniversalTensorSquare_sg27025
import Theorems.Thm_OAI_UniversalTensorSquare_sg27026
import Theorems.Thm_OAI_UniversalTensorSquare_sg27027
import Theorems.Thm_OAI_UniversalTensorSquare_sg27028
import Theorems.Thm_OAI_UniversalTensorSquare_sg27029
import Theorems.Thm_OAI_UniversalTensorSquare_sg295
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780
import Theorems.Thm_OAI_UniversalTensorSquare_sg8781
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert10

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert511 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 = 120 := by
  decide +kernel

lemma sg511 : RowSquare [3,3,2,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB511 sgT511 sgFlag511
  change solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB511 sgT511) sgFlag511 ≠ 0
  rw [sgCert511]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg27 : RowSquare [2,2,1] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1078 : RowSquare [6,4] [4,4,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
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

lemma sg291 : RowSquare [3,2,2,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10

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

lemma sg1720 : RowSquare [5,4,2,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg143

lemma sg1721 : RowSquare [5,4,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg291

lemma sg1827 : RowSquare [6,4,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg295

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

lemma sg2194 : RowSquare [6,4,2,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg511

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

lemma sg15564 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg7812

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

lemma sg17111 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg8780

lemma sg17126 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg8781

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 66. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27021 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1720 sg18245

lemma sg27022 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1827 sg17111

lemma sg27023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2194 sg15564

lemma sg27024 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg17126

lemma sg27030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1721 sg18245

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

lemma degreeTree43_259All_oai : degreeTree43_259.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27015,⟨sg27007,⟨sg27003,⟨sg27001,⟨sg27000,True.intro,True.intro⟩,⟨sg27002,True.intro,True.intro⟩⟩,⟨sg27005,⟨sg27004,True.intro,True.intro⟩,⟨sg27006,True.intro,True.intro⟩⟩⟩,⟨sg27011,⟨sg27009,⟨sg27008,True.intro,True.intro⟩,⟨sg27010,True.intro,True.intro⟩⟩,⟨sg27013,⟨sg27012,True.intro,True.intro⟩,⟨sg27014,True.intro,True.intro⟩⟩⟩⟩,⟨sg27023,⟨sg27019,⟨sg27017,⟨sg27016,True.intro,True.intro⟩,⟨sg27018,True.intro,True.intro⟩⟩,⟨sg27021,⟨sg27020,True.intro,True.intro⟩,⟨sg27022,True.intro,True.intro⟩⟩⟩,⟨sg27027,⟨sg27025,⟨sg27024,True.intro,True.intro⟩,⟨sg27026,True.intro,True.intro⟩⟩,⟨sg27029,⟨sg27028,True.intro,True.intro⟩,⟨sg27030,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_259All_oai := @OAI.UniversalTensorSquare.degreeTree43_259All_oai
