-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_480All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:55.567312+00:00
-- url     : https://prove2.me/submissions/331ec3b9-dd30-4235-a242-0a94c3cce3e6

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_479All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg29807
import Theorems.Thm_OAI_UniversalTensorSquare_sg29808
import Theorems.Thm_OAI_UniversalTensorSquare_sg29809
import Theorems.Thm_OAI_UniversalTensorSquare_sg29810
import Theorems.Thm_OAI_UniversalTensorSquare_sg29812
import Theorems.Thm_OAI_UniversalTensorSquare_sg29813
import Theorems.Thm_OAI_UniversalTensorSquare_sg29814
import Theorems.Thm_OAI_UniversalTensorSquare_sg29815
import Theorems.Thm_OAI_UniversalTensorSquare_sg29817
import Theorems.Thm_OAI_UniversalTensorSquare_sg29819
import Theorems.Thm_OAI_UniversalTensorSquare_sg29820
import Theorems.Thm_OAI_UniversalTensorSquare_sg29821
import Theorems.Thm_OAI_UniversalTensorSquare_sg29822
import Theorems.Thm_OAI_UniversalTensorSquare_sg29823
import Theorems.Thm_OAI_UniversalTensorSquare_sg29824
import Theorems.Thm_OAI_UniversalTensorSquare_sg29825
import Theorems.Thm_OAI_UniversalTensorSquare_sg29826
import Theorems.Thm_OAI_UniversalTensorSquare_sg29827
import Theorems.Thm_OAI_UniversalTensorSquare_sg29830
import Theorems.Thm_OAI_UniversalTensorSquare_sg29831
import Theorems.Thm_OAI_UniversalTensorSquare_sg29832
import Theorems.Thm_OAI_UniversalTensorSquare_sg29833
import Theorems.Thm_OAI_UniversalTensorSquare_sg29835
import Theorems.Thm_OAI_UniversalTensorSquare_sg29836
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg6563
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9285
import Theorems.Thm_OAI_UniversalTensorSquare_sg9909
import Theorems.Thm_OAI_UniversalTensorSquare_sg9945

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

lemma sg274 : RowSquare [3,2,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg33

lemma sg519 : RowSquare [4,1,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg675 : RowSquare [6,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

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

lemma sg710 : RowSquare [7,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg7 sg89

lemma sg1108 : RowSquare [7,2,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg89

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

lemma sg1352 : RowSquare [6,1,1,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg519

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

lemma sg5142 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg675 sg675

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

lemma sg5330 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg710

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6702 : RowSquare [5,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1108

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

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9251 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6563

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

lemma sg10352 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1352

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8806 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg274 sg2251

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

lemma sg10798 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5330

lemma sg10799 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg16 sg5142

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9606 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6702

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

lemma sg29811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9909

lemma sg29816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10798

lemma sg29818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9251

lemma sg29828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10799

lemma sg29829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9606

lemma sg29834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9945

lemma sg29837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9285

lemma sg29838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10352

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

lemma degreeTree43_478All : degreeTree43_478.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29822,⟨sg29814,⟨sg29810,⟨sg29808,⟨sg29807,True.intro,True.intro⟩,⟨sg29809,True.intro,True.intro⟩⟩,⟨sg29812,⟨sg29811,True.intro,True.intro⟩,⟨sg29813,True.intro,True.intro⟩⟩⟩,⟨sg29818,⟨sg29816,⟨sg29815,True.intro,True.intro⟩,⟨sg29817,True.intro,True.intro⟩⟩,⟨sg29820,⟨sg29819,True.intro,True.intro⟩,⟨sg29821,True.intro,True.intro⟩⟩⟩⟩,⟨sg29830,⟨sg29826,⟨sg29824,⟨sg29823,True.intro,True.intro⟩,⟨sg29825,True.intro,True.intro⟩⟩,⟨sg29828,⟨sg29827,True.intro,True.intro⟩,⟨sg29829,True.intro,True.intro⟩⟩⟩,⟨sg29834,⟨sg29832,⟨sg29831,True.intro,True.intro⟩,⟨sg29833,True.intro,True.intro⟩⟩,⟨sg29836,⟨sg29835,True.intro,True.intro⟩,⟨sg29837,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_480All_oai : degreeTree43_480.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29838,degreeTree43_478All,degreeTree43_479All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_480All_oai := @OAI.UniversalTensorSquare.degreeTree43_480All_oai
