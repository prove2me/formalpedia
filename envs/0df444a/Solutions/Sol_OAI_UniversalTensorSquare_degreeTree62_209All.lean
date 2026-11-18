-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_209All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:55:05.128758+00:00
-- url     : https://prove2.me/submissions/98742092-bd17-4453-88c3-949e9d3aa5f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17305
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg202
import Theorems.Thm_OAI_UniversalTensorSquare_sg20423
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg20508
import Theorems.Thm_OAI_UniversalTensorSquare_sg20510
import Theorems.Thm_OAI_UniversalTensorSquare_sg20511
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515
import Theorems.Thm_OAI_UniversalTensorSquare_sg20516
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2293
import Theorems.Thm_OAI_UniversalTensorSquare_sg232
import Theorems.Thm_OAI_UniversalTensorSquare_sg2406
import Theorems.Thm_OAI_UniversalTensorSquare_sg2706
import Theorems.Thm_OAI_UniversalTensorSquare_sg2806
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg3069
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34357
import Theorems.Thm_OAI_UniversalTensorSquare_sg34360
import Theorems.Thm_OAI_UniversalTensorSquare_sg34362
import Theorems.Thm_OAI_UniversalTensorSquare_sg34364
import Theorems.Thm_OAI_UniversalTensorSquare_sg34365
import Theorems.Thm_OAI_UniversalTensorSquare_sg34366
import Theorems.Thm_OAI_UniversalTensorSquare_sg34368
import Theorems.Thm_OAI_UniversalTensorSquare_sg34369
import Theorems.Thm_OAI_UniversalTensorSquare_sg34371
import Theorems.Thm_OAI_UniversalTensorSquare_sg348
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg4834
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg551
import Theorems.Thm_OAI_UniversalTensorSquare_sg564
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

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

lemma sg2212 : RowSquare [6,4,3] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg306

lemma sg2329 : RowSquare [7,3,3] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg348

lemma sg2391 : RowSquare [8,2,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg178

lemma sg2392 : RowSquare [8,2,2,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg371

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

lemma sg2631 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg111

lemma sg2773 : RowSquare [7,3,3,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg551

lemma sg2807 : RowSquare [7,4,2,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg564

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2961 : RowSquare [8,3,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1000

lemma sg3127 : RowSquare [9,2,2,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg372

lemma sg3259 : RowSquare [5,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg910

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

lemma sg4347 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg430

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

lemma sg13538 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2212 sg3127

lemma sg13736 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2807

lemma sg13737 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2392 sg2806

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

lemma sg13754 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2406 sg2773

lemma sg14048 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg3069

lemma sg14049 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2329 sg2961

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

lemma sg14468 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2631

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16342 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13538

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

lemma sg17346 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18167 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14048

lemma sg18168 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14049

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

lemma sg20422 : RowSquare [8,8,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3259 sg4347

lemma sg20517 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2706 sg4834

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

lemma sg20697 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14468

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

lemma sg17314 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13736

lemma sg17315 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13737

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

lemma sg34354 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17314

lemma sg34355 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18167

lemma sg34356 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17314

lemma sg34358 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16342

lemma sg34359 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17305

lemma sg34361 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17346

lemma sg34363 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17346

lemma sg34367 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17346

lemma sg34370 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17314

lemma sg34372 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17314

lemma sg34373 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17315

lemma sg34374 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,9,6,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18168

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

lemma degreeTree62_209All_oai : degreeTree62_209.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34364,⟨sg34359,⟨sg34356,⟨sg34355,⟨sg34354,True.intro,True.intro⟩,True.intro⟩,⟨sg34358,⟨sg34357,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34362,⟨sg34361,⟨sg34360,True.intro,True.intro⟩,True.intro⟩,⟨sg34363,True.intro,True.intro⟩⟩⟩,⟨sg34370,⟨sg34367,⟨sg34366,⟨sg34365,True.intro,True.intro⟩,True.intro⟩,⟨sg34369,⟨sg34368,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34373,⟨sg34372,⟨sg34371,True.intro,True.intro⟩,True.intro⟩,⟨sg34374,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_209All_oai := @OAI.UniversalTensorSquare.degreeTree62_209All_oai
