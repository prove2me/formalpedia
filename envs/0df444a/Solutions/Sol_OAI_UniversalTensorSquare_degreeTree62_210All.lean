-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_210All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:02:36.182075+00:00
-- url     : https://prove2.me/submissions/c9db9170-0e59-4a58-936c-f114f4d384e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_209All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1032
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg13735
import Theorems.Thm_OAI_UniversalTensorSquare_sg16341
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17312
import Theorems.Thm_OAI_UniversalTensorSquare_sg17345
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg19623
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515
import Theorems.Thm_OAI_UniversalTensorSquare_sg20516
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2373
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg314
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34333
import Theorems.Thm_OAI_UniversalTensorSquare_sg34336
import Theorems.Thm_OAI_UniversalTensorSquare_sg34339
import Theorems.Thm_OAI_UniversalTensorSquare_sg34340
import Theorems.Thm_OAI_UniversalTensorSquare_sg34342
import Theorems.Thm_OAI_UniversalTensorSquare_sg34343
import Theorems.Thm_OAI_UniversalTensorSquare_sg34345
import Theorems.Thm_OAI_UniversalTensorSquare_sg34348
import Theorems.Thm_OAI_UniversalTensorSquare_sg34349
import Theorems.Thm_OAI_UniversalTensorSquare_sg34350
import Theorems.Thm_OAI_UniversalTensorSquare_sg34351
import Theorems.Thm_OAI_UniversalTensorSquare_sg34353
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg52

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

lemma sgCert144 : solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 = 2 := by
  decide +kernel

lemma sg144 : RowSquare [3,2,1,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB144 sgT144 sgFlag144
  change solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 ≠ 0
  rw [sgCert144]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert166 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 = 3 := by
  decide +kernel

lemma sg166 : RowSquare [3,3,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB166 sgT166 sgFlag166
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 ≠ 0
  rw [sgCert166]
  norm_num

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

lemma sg254 : RowSquare [2,2,2,2] [2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13

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

lemma sg914 : RowSquare [5,2,1,1,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg52

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

lemma sg2433 : RowSquare [8,3,2] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg390

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

lemma sg2763 : RowSquare [7,3,2,2] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg144

lemma sg2783 : RowSquare [7,4,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg914

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3725 : RowSquare [9,3,2,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1032

lemma sg4044 : RowSquare [6,3,3,3,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg314 sg254

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

lemma sg13752 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2433 sg2763

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14140 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2373 sg2783

lemma sg14471 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2633

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

lemma sg15795 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg3725 sg4044

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17344 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13752

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

lemma sg18934 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14140

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

lemma sg20700 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14471

lemma sg20852 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11748

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

lemma sg17313 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 84. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34332 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17344

lemma sg34334 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17312

lemma sg34335 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17345

lemma sg34337 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17345

lemma sg34338 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg18934

lemma sg34341 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17345

lemma sg34344 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17313

lemma sg34346 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17313

lemma sg34347 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16341

lemma sg34352 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15795

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

lemma degreeTree62_208All : degreeTree62_208.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34342,⟨sg34337,⟨sg34334,⟨sg34333,⟨sg34332,True.intro,True.intro⟩,True.intro⟩,⟨sg34336,⟨sg34335,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34340,⟨sg34339,⟨sg34338,True.intro,True.intro⟩,True.intro⟩,⟨sg34341,True.intro,True.intro⟩⟩⟩,⟨sg34348,⟨sg34345,⟨sg34344,⟨sg34343,True.intro,True.intro⟩,True.intro⟩,⟨sg34347,⟨sg34346,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34351,⟨sg34350,⟨sg34349,True.intro,True.intro⟩,True.intro⟩,⟨sg34352,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_210All_oai : degreeTree62_210.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34353,degreeTree62_208All,degreeTree62_209All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_210All_oai := @OAI.UniversalTensorSquare.degreeTree62_210All_oai
