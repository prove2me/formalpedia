-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_17All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:39:33.915812+00:00
-- url     : https://prove2.me/submissions/62ea2df8-9495-4af0-99df-868139f49545
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_16All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg12087
import Theorems.Thm_OAI_UniversalTensorSquare_sg12088
import Theorems.Thm_OAI_UniversalTensorSquare_sg12089
import Theorems.Thm_OAI_UniversalTensorSquare_sg12090
import Theorems.Thm_OAI_UniversalTensorSquare_sg12091
import Theorems.Thm_OAI_UniversalTensorSquare_sg12092
import Theorems.Thm_OAI_UniversalTensorSquare_sg12094
import Theorems.Thm_OAI_UniversalTensorSquare_sg12095
import Theorems.Thm_OAI_UniversalTensorSquare_sg12096
import Theorems.Thm_OAI_UniversalTensorSquare_sg12097
import Theorems.Thm_OAI_UniversalTensorSquare_sg12099
import Theorems.Thm_OAI_UniversalTensorSquare_sg12101
import Theorems.Thm_OAI_UniversalTensorSquare_sg12102
import Theorems.Thm_OAI_UniversalTensorSquare_sg12103
import Theorems.Thm_OAI_UniversalTensorSquare_sg12105
import Theorems.Thm_OAI_UniversalTensorSquare_sg12108
import Theorems.Thm_OAI_UniversalTensorSquare_sg12109
import Theorems.Thm_OAI_UniversalTensorSquare_sg12110
import Theorems.Thm_OAI_UniversalTensorSquare_sg12111
import Theorems.Thm_OAI_UniversalTensorSquare_sg12113
import Theorems.Thm_OAI_UniversalTensorSquare_sg12115
import Theorems.Thm_OAI_UniversalTensorSquare_sg12116
import Theorems.Thm_OAI_UniversalTensorSquare_sg122
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2583
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg348
import Theorems.Thm_OAI_UniversalTensorSquare_sg5283
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg11 : RowSquare [2,1,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg57 : RowSquare [2,2,1,1] [3,2,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg98 : RowSquare [4,2] [3,1,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg99 : RowSquare [4,2] [3,2,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg100 : RowSquare [4,2] [4,1,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
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

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg90 : RowSquare [4,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg150 : RowSquare [3,2,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg57

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

lemma sg764 : RowSquare [3,3,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg33

lemma sg769 : RowSquare [3,3,1,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg348

lemma sg770 : RowSquare [3,3,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg33 sg33

lemma sg1203 : RowSquare [4,3,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

lemma sg1210 : RowSquare [4,3,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg178

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

lemma sg2039 : RowSquare [4,3,1,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

lemma sg2045 : RowSquare [4,3,1,1,1,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg178

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

lemma sg2577 : RowSquare [5,3,1,1,1,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg586

lemma sg2603 : RowSquare [5,4,2,2,1] [3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg150 sg122

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

lemma sg5282 : RowSquare [4,4,2,2,2,2,1,1] [4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg1650

lemma sg5287 : RowSquare [4,4,2,2,2,2,1,1] [5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg1650

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6140 : RowSquare [5,4,2,2,2,2,1,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2603

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

lemma sg12093 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5282

lemma sg12098 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6140

lemma sg12100 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg769 sg2577

lemma sg12104 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1210 sg2039

lemma sg12106 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5287

lemma sg12107 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5283

lemma sg12112 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2583

lemma sg12114 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2045

lemma sg12117 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg2577

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree24_15All : degreeTree24_15.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12102,⟨sg12094,⟨sg12090,⟨sg12088,⟨sg12087,True.intro,True.intro⟩,⟨sg12089,True.intro,True.intro⟩⟩,⟨sg12092,⟨sg12091,True.intro,True.intro⟩,⟨sg12093,True.intro,True.intro⟩⟩⟩,⟨sg12098,⟨sg12096,⟨sg12095,True.intro,True.intro⟩,⟨sg12097,True.intro,True.intro⟩⟩,⟨sg12100,⟨sg12099,True.intro,True.intro⟩,⟨sg12101,True.intro,True.intro⟩⟩⟩⟩,⟨sg12110,⟨sg12106,⟨sg12104,⟨sg12103,True.intro,True.intro⟩,⟨sg12105,True.intro,True.intro⟩⟩,⟨sg12108,⟨sg12107,True.intro,True.intro⟩,⟨sg12109,True.intro,True.intro⟩⟩⟩,⟨sg12114,⟨sg12112,⟨sg12111,True.intro,True.intro⟩,⟨sg12113,True.intro,True.intro⟩⟩,⟨sg12116,⟨sg12115,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_17All_oai : degreeTree24_17.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12117,degreeTree24_15All,degreeTree24_16All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_17All_oai := @OAI.UniversalTensorSquare.degreeTree24_17All_oai
