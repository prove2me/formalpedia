-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_551All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:47:53.858929+00:00
-- url     : https://prove2.me/submissions/f67b7cd7-82e9-4377-afad-4814d3aa5c31

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg10867
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg166
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1814
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg295
import Theorems.Thm_OAI_UniversalTensorSquare_sg30714
import Theorems.Thm_OAI_UniversalTensorSquare_sg30715
import Theorems.Thm_OAI_UniversalTensorSquare_sg30716
import Theorems.Thm_OAI_UniversalTensorSquare_sg30717
import Theorems.Thm_OAI_UniversalTensorSquare_sg30718
import Theorems.Thm_OAI_UniversalTensorSquare_sg30719
import Theorems.Thm_OAI_UniversalTensorSquare_sg30721
import Theorems.Thm_OAI_UniversalTensorSquare_sg30722
import Theorems.Thm_OAI_UniversalTensorSquare_sg30724
import Theorems.Thm_OAI_UniversalTensorSquare_sg30725
import Theorems.Thm_OAI_UniversalTensorSquare_sg30726
import Theorems.Thm_OAI_UniversalTensorSquare_sg30727
import Theorems.Thm_OAI_UniversalTensorSquare_sg30728
import Theorems.Thm_OAI_UniversalTensorSquare_sg30729
import Theorems.Thm_OAI_UniversalTensorSquare_sg30731
import Theorems.Thm_OAI_UniversalTensorSquare_sg30732
import Theorems.Thm_OAI_UniversalTensorSquare_sg30735
import Theorems.Thm_OAI_UniversalTensorSquare_sg30736
import Theorems.Thm_OAI_UniversalTensorSquare_sg30739
import Theorems.Thm_OAI_UniversalTensorSquare_sg30740
import Theorems.Thm_OAI_UniversalTensorSquare_sg30741
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg42
import Theorems.Thm_OAI_UniversalTensorSquare_sg562
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg595
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg789
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg27 : RowSquare [2,2,1] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg666 : RowSquare [5,4] [5,4] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1082 : RowSquare [6,4] [5,4,1] := by
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

lemma sg243 : RowSquare [2,2,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg16 sg18

lemma sg291 : RowSquare [3,2,2,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10

lemma sg530 : RowSquare [4,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

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

lemma sg784 : RowSquare [3,3,1,1,1,1] [7,2,1] := by
  exact rowSquare_join (by decide) sg1 sg243

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

lemma sg1720 : RowSquare [5,4,2,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg143

lemma sg1721 : RowSquare [5,4,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg291

lemma sg1827 : RowSquare [6,4,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg295

lemma sg1836 : RowSquare [6,4,1,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg143

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

lemma sg2223 : RowSquare [6,5,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg562

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

lemma sg3870 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg371

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

lemma sg5536 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg595

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

lemma sg7823 : RowSquare [6,6,2,2,2,2] [3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg784 sg789

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

lemma sg8366 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg1682

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

lemma sg12632 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg4160

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

lemma sg15571 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg7812

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

lemma sg17110 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7812

lemma sg17122 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg8780

lemma sg17138 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7823

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 75. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1720 sg18255

lemma sg30712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1827 sg17122

lemma sg30713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2194 sg15571

lemma sg30720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1721 sg18255

lemma sg30723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15549

lemma sg30730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1836 sg17110

lemma sg30733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg17138

lemma sg30734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5536 sg12632

lemma sg30737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8366 sg10682

lemma sg30738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14520

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

lemma degreeTree43_551All_oai : degreeTree43_551.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30726,⟨sg30718,⟨sg30714,⟨sg30712,⟨sg30711,True.intro,True.intro⟩,⟨sg30713,True.intro,True.intro⟩⟩,⟨sg30716,⟨sg30715,True.intro,True.intro⟩,⟨sg30717,True.intro,True.intro⟩⟩⟩,⟨sg30722,⟨sg30720,⟨sg30719,True.intro,True.intro⟩,⟨sg30721,True.intro,True.intro⟩⟩,⟨sg30724,⟨sg30723,True.intro,True.intro⟩,⟨sg30725,True.intro,True.intro⟩⟩⟩⟩,⟨sg30734,⟨sg30730,⟨sg30728,⟨sg30727,True.intro,True.intro⟩,⟨sg30729,True.intro,True.intro⟩⟩,⟨sg30732,⟨sg30731,True.intro,True.intro⟩,⟨sg30733,True.intro,True.intro⟩⟩⟩,⟨sg30738,⟨sg30736,⟨sg30735,True.intro,True.intro⟩,⟨sg30737,True.intro,True.intro⟩⟩,⟨sg30740,⟨sg30739,True.intro,True.intro⟩,⟨sg30741,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_551All_oai := @OAI.UniversalTensorSquare.degreeTree43_551All_oai
