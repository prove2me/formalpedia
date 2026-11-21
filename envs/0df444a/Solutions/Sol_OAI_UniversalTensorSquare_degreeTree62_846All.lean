-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_846All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:59:20.541204+00:00
-- url     : https://prove2.me/submissions/64077203-d2ba-4203-ad7a-64b7cd595416

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_844All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg41326
import Theorems.Thm_OAI_UniversalTensorSquare_sg41327
import Theorems.Thm_OAI_UniversalTensorSquare_sg41328
import Theorems.Thm_OAI_UniversalTensorSquare_sg41330
import Theorems.Thm_OAI_UniversalTensorSquare_sg41331
import Theorems.Thm_OAI_UniversalTensorSquare_sg41332
import Theorems.Thm_OAI_UniversalTensorSquare_sg41334
import Theorems.Thm_OAI_UniversalTensorSquare_sg41335
import Theorems.Thm_OAI_UniversalTensorSquare_sg41336
import Theorems.Thm_OAI_UniversalTensorSquare_sg41337
import Theorems.Thm_OAI_UniversalTensorSquare_sg41338
import Theorems.Thm_OAI_UniversalTensorSquare_sg41339
import Theorems.Thm_OAI_UniversalTensorSquare_sg41340
import Theorems.Thm_OAI_UniversalTensorSquare_sg41341
import Theorems.Thm_OAI_UniversalTensorSquare_sg41342
import Theorems.Thm_OAI_UniversalTensorSquare_sg41343
import Theorems.Thm_OAI_UniversalTensorSquare_sg41344
import Theorems.Thm_OAI_UniversalTensorSquare_sg41345
import Theorems.Thm_OAI_UniversalTensorSquare_sg41346
import Theorems.Thm_OAI_UniversalTensorSquare_sg41347

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert168 : solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 = 6 := by
  decide +kernel

lemma sg168 : RowSquare [3,3,1] [3,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB168 sgT168 sgFlag168
  change solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 ≠ 0
  rw [sgCert168]
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

lemma sg59 : RowSquare [2,2,1,1] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg130 : RowSquare [2,2,2,1] [5,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
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

lemma sg364 : RowSquare [4,4] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

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

lemma sg2003 : RowSquare [9,2,1] [6,2,2,2] := by
  exact rowSquare_join (by decide) sg20 sg390

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

lemma sg2110 : RowSquare [4,4,3,2] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg130

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2614 : RowSquare [5,4,3,2] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2110

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

lemma sg4525 : RowSquare [10,2,2,2] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg373

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11748 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2251

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

lemma sg11108 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2003

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15339 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4525

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15872 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15339

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

lemma sg20070 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11108

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

lemma sg20858 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg168 sg11748

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 101. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41329 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,8,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20070

lemma sg41333 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,9,9,8,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15872

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

lemma degreeTree62_845All : degreeTree62_845.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41337,⟨sg41332,⟨sg41329,⟨sg41328,⟨sg41327,True.intro,True.intro⟩,True.intro⟩,⟨sg41331,⟨sg41330,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41335,⟨sg41334,⟨sg41333,True.intro,True.intro⟩,True.intro⟩,⟨sg41336,True.intro,True.intro⟩⟩⟩,⟨sg41343,⟨sg41340,⟨sg41339,⟨sg41338,True.intro,True.intro⟩,True.intro⟩,⟨sg41342,⟨sg41341,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41346,⟨sg41345,⟨sg41344,True.intro,True.intro⟩,True.intro⟩,⟨sg41347,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_846All_oai : degreeTree62_846.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41326,degreeTree62_844All,degreeTree62_845All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_846All_oai := @OAI.UniversalTensorSquare.degreeTree62_846All_oai
