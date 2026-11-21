-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_461All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:24.957212+00:00
-- url     : https://prove2.me/submissions/e45564d3-4001-4d30-aa44-d6777b7f3306

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_459All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg29582
import Theorems.Thm_OAI_UniversalTensorSquare_sg29583
import Theorems.Thm_OAI_UniversalTensorSquare_sg29584
import Theorems.Thm_OAI_UniversalTensorSquare_sg29585
import Theorems.Thm_OAI_UniversalTensorSquare_sg29587
import Theorems.Thm_OAI_UniversalTensorSquare_sg29588
import Theorems.Thm_OAI_UniversalTensorSquare_sg29589
import Theorems.Thm_OAI_UniversalTensorSquare_sg29590
import Theorems.Thm_OAI_UniversalTensorSquare_sg29591
import Theorems.Thm_OAI_UniversalTensorSquare_sg29592
import Theorems.Thm_OAI_UniversalTensorSquare_sg29594
import Theorems.Thm_OAI_UniversalTensorSquare_sg29596
import Theorems.Thm_OAI_UniversalTensorSquare_sg29597
import Theorems.Thm_OAI_UniversalTensorSquare_sg29598
import Theorems.Thm_OAI_UniversalTensorSquare_sg29599
import Theorems.Thm_OAI_UniversalTensorSquare_sg29601
import Theorems.Thm_OAI_UniversalTensorSquare_sg29603
import Theorems.Thm_OAI_UniversalTensorSquare_sg29604
import Theorems.Thm_OAI_UniversalTensorSquare_sg29605
import Theorems.Thm_OAI_UniversalTensorSquare_sg29607
import Theorems.Thm_OAI_UniversalTensorSquare_sg29608
import Theorems.Thm_OAI_UniversalTensorSquare_sg29609
import Theorems.Thm_OAI_UniversalTensorSquare_sg29610
import Theorems.Thm_OAI_UniversalTensorSquare_sg29611
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg378
import Theorems.Thm_OAI_UniversalTensorSquare_sg4161
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg5736
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6915
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg70 : RowSquare [3,1,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

lemma sg528 : RowSquare [4,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg262

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg681 : RowSquare [6,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

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

lemma sg1054 : RowSquare [6,2,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg16 sg70

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

lemma sg1404 : RowSquare [6,2,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg16 sg136

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

lemma sg5153 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg681

lemma sg5326 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg710

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

lemma sg3869 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg373

lemma sg3872 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg373

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

lemma sg6764 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1041

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

lemma sg8414 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg2626

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

lemma sg10463 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5153

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

lemma sg9899 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1404

lemma sg9935 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6764

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

lemma sg8732 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg1754

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

lemma sg10792 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5326

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11479 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg4161

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

lemma sg9542 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1054 sg1754

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

lemma sg14515 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg5735

lemma sg14519 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg5736

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 72. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14515

lemma sg29581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14519

lemma sg29586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9542

lemma sg29593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9899

lemma sg29595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11479

lemma sg29600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10463

lemma sg29602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10792

lemma sg29606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9935

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

lemma degreeTree43_460All : degreeTree43_460.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29596,⟨sg29588,⟨sg29584,⟨sg29582,⟨sg29581,True.intro,True.intro⟩,⟨sg29583,True.intro,True.intro⟩⟩,⟨sg29586,⟨sg29585,True.intro,True.intro⟩,⟨sg29587,True.intro,True.intro⟩⟩⟩,⟨sg29592,⟨sg29590,⟨sg29589,True.intro,True.intro⟩,⟨sg29591,True.intro,True.intro⟩⟩,⟨sg29594,⟨sg29593,True.intro,True.intro⟩,⟨sg29595,True.intro,True.intro⟩⟩⟩⟩,⟨sg29604,⟨sg29600,⟨sg29598,⟨sg29597,True.intro,True.intro⟩,⟨sg29599,True.intro,True.intro⟩⟩,⟨sg29602,⟨sg29601,True.intro,True.intro⟩,⟨sg29603,True.intro,True.intro⟩⟩⟩,⟨sg29608,⟨sg29606,⟨sg29605,True.intro,True.intro⟩,⟨sg29607,True.intro,True.intro⟩⟩,⟨sg29610,⟨sg29609,True.intro,True.intro⟩,⟨sg29611,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_461All_oai : degreeTree43_461.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29580,degreeTree43_459All,degreeTree43_460All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_461All_oai := @OAI.UniversalTensorSquare.degreeTree43_461All_oai
