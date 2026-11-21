-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_489All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:51:39.448732+00:00
-- url     : https://prove2.me/submissions/b0e27ef0-93e2-4e11-b90b-13101f558f59

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg29904
import Theorems.Thm_OAI_UniversalTensorSquare_sg29905
import Theorems.Thm_OAI_UniversalTensorSquare_sg29906
import Theorems.Thm_OAI_UniversalTensorSquare_sg29908
import Theorems.Thm_OAI_UniversalTensorSquare_sg29909
import Theorems.Thm_OAI_UniversalTensorSquare_sg29910
import Theorems.Thm_OAI_UniversalTensorSquare_sg29912
import Theorems.Thm_OAI_UniversalTensorSquare_sg29914
import Theorems.Thm_OAI_UniversalTensorSquare_sg29915
import Theorems.Thm_OAI_UniversalTensorSquare_sg29916
import Theorems.Thm_OAI_UniversalTensorSquare_sg29917
import Theorems.Thm_OAI_UniversalTensorSquare_sg29919
import Theorems.Thm_OAI_UniversalTensorSquare_sg29920
import Theorems.Thm_OAI_UniversalTensorSquare_sg29922
import Theorems.Thm_OAI_UniversalTensorSquare_sg29923
import Theorems.Thm_OAI_UniversalTensorSquare_sg29924
import Theorems.Thm_OAI_UniversalTensorSquare_sg29925
import Theorems.Thm_OAI_UniversalTensorSquare_sg29927
import Theorems.Thm_OAI_UniversalTensorSquare_sg29928
import Theorems.Thm_OAI_UniversalTensorSquare_sg29929
import Theorems.Thm_OAI_UniversalTensorSquare_sg29932
import Theorems.Thm_OAI_UniversalTensorSquare_sg29933
import Theorems.Thm_OAI_UniversalTensorSquare_sg29934
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg590
import Theorems.Thm_OAI_UniversalTensorSquare_sg637
import Theorems.Thm_OAI_UniversalTensorSquare_sg6942
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg9290
import Theorems.Thm_OAI_UniversalTensorSquare_sg9291

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
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

lemma sg594 : RowSquare [5,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg315

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg676 : RowSquare [6,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg692 : RowSquare [6,2,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg32

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

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg5066 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg692 sg676

lemma sg5138 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg676

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

lemma sg3875 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg373

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

lemma sg4575 : RowSquare [3,3,3,2,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg390 sg637

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5582 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg3875

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6013 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg4575

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6941 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1005

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10358 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5138

lemma sg10359 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6941

lemma sg10360 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg6942

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9948 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5066

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

lemma sg11829 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg3521

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

lemma sg12618 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg4160

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

lemma sg29907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9948

lemma sg29911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9290

lemma sg29913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10358

lemma sg29918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9291

lemma sg29921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10359

lemma sg29926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10360

lemma sg29930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5582 sg12618

lemma sg29931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6013 sg11829

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

lemma degreeTree43_489All_oai : degreeTree43_489.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29919,⟨sg29911,⟨sg29907,⟨sg29905,⟨sg29904,True.intro,True.intro⟩,⟨sg29906,True.intro,True.intro⟩⟩,⟨sg29909,⟨sg29908,True.intro,True.intro⟩,⟨sg29910,True.intro,True.intro⟩⟩⟩,⟨sg29915,⟨sg29913,⟨sg29912,True.intro,True.intro⟩,⟨sg29914,True.intro,True.intro⟩⟩,⟨sg29917,⟨sg29916,True.intro,True.intro⟩,⟨sg29918,True.intro,True.intro⟩⟩⟩⟩,⟨sg29927,⟨sg29923,⟨sg29921,⟨sg29920,True.intro,True.intro⟩,⟨sg29922,True.intro,True.intro⟩⟩,⟨sg29925,⟨sg29924,True.intro,True.intro⟩,⟨sg29926,True.intro,True.intro⟩⟩⟩,⟨sg29931,⟨sg29929,⟨sg29928,True.intro,True.intro⟩,⟨sg29930,True.intro,True.intro⟩⟩,⟨sg29933,⟨sg29932,True.intro,True.intro⟩,⟨sg29934,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_489All_oai := @OAI.UniversalTensorSquare.degreeTree43_489All_oai
