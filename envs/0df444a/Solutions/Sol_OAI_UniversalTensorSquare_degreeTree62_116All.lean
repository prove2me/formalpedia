-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_116All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:01:14.143849+00:00
-- url     : https://prove2.me/submissions/9ea02b57-00f5-4319-94db-675905bcffd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg1891
import Theorems.Thm_OAI_UniversalTensorSquare_sg20423
import Theorems.Thm_OAI_UniversalTensorSquare_sg20510
import Theorems.Thm_OAI_UniversalTensorSquare_sg20511
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515
import Theorems.Thm_OAI_UniversalTensorSquare_sg2314
import Theorems.Thm_OAI_UniversalTensorSquare_sg26
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33323
import Theorems.Thm_OAI_UniversalTensorSquare_sg33324
import Theorems.Thm_OAI_UniversalTensorSquare_sg33325
import Theorems.Thm_OAI_UniversalTensorSquare_sg33326
import Theorems.Thm_OAI_UniversalTensorSquare_sg33327
import Theorems.Thm_OAI_UniversalTensorSquare_sg33328
import Theorems.Thm_OAI_UniversalTensorSquare_sg33329
import Theorems.Thm_OAI_UniversalTensorSquare_sg33330
import Theorems.Thm_OAI_UniversalTensorSquare_sg33331
import Theorems.Thm_OAI_UniversalTensorSquare_sg33332
import Theorems.Thm_OAI_UniversalTensorSquare_sg33333
import Theorems.Thm_OAI_UniversalTensorSquare_sg33335
import Theorems.Thm_OAI_UniversalTensorSquare_sg33339
import Theorems.Thm_OAI_UniversalTensorSquare_sg33340
import Theorems.Thm_OAI_UniversalTensorSquare_sg33341
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg564
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg87
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
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

lemma sg644 : RowSquare [5,3,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg32

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

lemma sg1136 : RowSquare [3,1,1,1,1,1,1,1,1] [8,3] := by
  exact rowSquare_join (by decide) sg49 sg92

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

lemma sg2390 : RowSquare [8,2,2,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

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

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

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

lemma sg3009 : RowSquare [8,3,2,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg616

lemma sg3103 : RowSquare [8,4,2] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg644

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

lemma sg4931 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg1136

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

lemma sg13706 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2807

lemma sg13707 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg2314 sg3009

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12769 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3103

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

lemma sg16728 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12769

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

lemma sg18146 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12769

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

lemma sg20634 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4931

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

lemma sg17275 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13706

lemma sg17276 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13707

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

lemma sg33334 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17276

lemma sg33336 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17276

lemma sg33337 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17275

lemma sg33338 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18146

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 82. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33342 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16728

lemma sg33343 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17275

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

lemma degreeTree62_116All_oai : degreeTree62_116.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33333,⟨sg33328,⟨sg33325,⟨sg33324,⟨sg33323,True.intro,True.intro⟩,True.intro⟩,⟨sg33327,⟨sg33326,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33331,⟨sg33330,⟨sg33329,True.intro,True.intro⟩,True.intro⟩,⟨sg33332,True.intro,True.intro⟩⟩⟩,⟨sg33339,⟨sg33336,⟨sg33335,⟨sg33334,True.intro,True.intro⟩,True.intro⟩,⟨sg33338,⟨sg33337,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33342,⟨sg33341,⟨sg33340,True.intro,True.intro⟩,True.intro⟩,⟨sg33343,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_116All_oai := @OAI.UniversalTensorSquare.degreeTree62_116All_oai
