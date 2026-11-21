-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_495All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:45:22.136618+00:00
-- url     : https://prove2.me/submissions/fa27e98b-3ebd-4c7c-b115-a9791ddd106a

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_493All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10867
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg166
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg1823
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg21224
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg23
import Theorems.Thm_OAI_UniversalTensorSquare_sg26
import Theorems.Thm_OAI_UniversalTensorSquare_sg29968
import Theorems.Thm_OAI_UniversalTensorSquare_sg29969
import Theorems.Thm_OAI_UniversalTensorSquare_sg29970
import Theorems.Thm_OAI_UniversalTensorSquare_sg29971
import Theorems.Thm_OAI_UniversalTensorSquare_sg29972
import Theorems.Thm_OAI_UniversalTensorSquare_sg29974
import Theorems.Thm_OAI_UniversalTensorSquare_sg29977
import Theorems.Thm_OAI_UniversalTensorSquare_sg29978
import Theorems.Thm_OAI_UniversalTensorSquare_sg29980
import Theorems.Thm_OAI_UniversalTensorSquare_sg29981
import Theorems.Thm_OAI_UniversalTensorSquare_sg29982
import Theorems.Thm_OAI_UniversalTensorSquare_sg29983
import Theorems.Thm_OAI_UniversalTensorSquare_sg29985
import Theorems.Thm_OAI_UniversalTensorSquare_sg29986
import Theorems.Thm_OAI_UniversalTensorSquare_sg29987
import Theorems.Thm_OAI_UniversalTensorSquare_sg29988
import Theorems.Thm_OAI_UniversalTensorSquare_sg29989
import Theorems.Thm_OAI_UniversalTensorSquare_sg29990
import Theorems.Thm_OAI_UniversalTensorSquare_sg29991
import Theorems.Thm_OAI_UniversalTensorSquare_sg29993
import Theorems.Thm_OAI_UniversalTensorSquare_sg29994
import Theorems.Thm_OAI_UniversalTensorSquare_sg29995
import Theorems.Thm_OAI_UniversalTensorSquare_sg29996
import Theorems.Thm_OAI_UniversalTensorSquare_sg29998
import Theorems.Thm_OAI_UniversalTensorSquare_sg29999
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg561
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg789

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

lemma sgCert549 : solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB549 sgT549) sgFlag549 = -8 := by
  decide +kernel

lemma sg549 : RowSquare [4,2,2,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,2,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB549 sgT549 sgFlag549
  change solveCompact 9 (.full [7,2]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [7,2] (Equiv.refl (Fin 9)) sgB549 sgT549) sgFlag549 ≠ 0
  rw [sgCert549]
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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg666 : RowSquare [5,4] [5,4] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1086 : RowSquare [6,4] [6,4] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1493 : RowSquare [6,5] [6,5] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
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

lemma sg247 : RowSquare [2,2,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg19

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg530 : RowSquare [4,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

lemma sg573 : RowSquare [4,3,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg23

lemma sg592 : RowSquare [5,1,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg313

lemma sg607 : RowSquare [5,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg788 : RowSquare [3,3,1,1,1,1] [9,1] := by
  exact rowSquare_join (by decide) sg1 sg247

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

lemma sg1468 : RowSquare [6,4,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg166

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

lemma sg1716 : RowSquare [5,4,2,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg26 sg143

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

lemma sg2179 : RowSquare [6,4,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg549

lemma sg2222 : RowSquare [6,5,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg561

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

lemma sg3867 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg371

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7813 : RowSquare [6,6,2,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg788 sg789

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8355 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg592 sg1682

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10682 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg2251

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

lemma sg14520 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg530 sg5735

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

lemma sg15549 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg6457

lemma sg15583 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg7812

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

lemma sg18255 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg10867

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

lemma sg17123 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7813

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 73. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29973 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1716 sg18255

lemma sg29975 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2179 sg15583

lemma sg29976 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2222 sg15549

lemma sg29979 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg573 sg21224

lemma sg29984 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1823 sg17123

lemma sg29992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3867 sg14520

lemma sg29997 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8355 sg10682

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

lemma degreeTree43_494All : degreeTree43_494.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29984,⟨sg29976,⟨sg29972,⟨sg29970,⟨sg29969,True.intro,True.intro⟩,⟨sg29971,True.intro,True.intro⟩⟩,⟨sg29974,⟨sg29973,True.intro,True.intro⟩,⟨sg29975,True.intro,True.intro⟩⟩⟩,⟨sg29980,⟨sg29978,⟨sg29977,True.intro,True.intro⟩,⟨sg29979,True.intro,True.intro⟩⟩,⟨sg29982,⟨sg29981,True.intro,True.intro⟩,⟨sg29983,True.intro,True.intro⟩⟩⟩⟩,⟨sg29992,⟨sg29988,⟨sg29986,⟨sg29985,True.intro,True.intro⟩,⟨sg29987,True.intro,True.intro⟩⟩,⟨sg29990,⟨sg29989,True.intro,True.intro⟩,⟨sg29991,True.intro,True.intro⟩⟩⟩,⟨sg29996,⟨sg29994,⟨sg29993,True.intro,True.intro⟩,⟨sg29995,True.intro,True.intro⟩⟩,⟨sg29998,⟨sg29997,True.intro,True.intro⟩,⟨sg29999,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_495All_oai : degreeTree43_495.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29968,degreeTree43_493All,degreeTree43_494All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_495All_oai := @OAI.UniversalTensorSquare.degreeTree43_495All_oai
