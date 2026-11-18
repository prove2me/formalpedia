-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_598All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:09:38.889878+00:00
-- url     : https://prove2.me/submissions/e72d6e19-af6c-448d-a594-900358c99522
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg10408
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg236
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg275
import Theorems.Thm_OAI_UniversalTensorSquare_sg31325
import Theorems.Thm_OAI_UniversalTensorSquare_sg31329
import Theorems.Thm_OAI_UniversalTensorSquare_sg31333
import Theorems.Thm_OAI_UniversalTensorSquare_sg31334
import Theorems.Thm_OAI_UniversalTensorSquare_sg31335
import Theorems.Thm_OAI_UniversalTensorSquare_sg31336
import Theorems.Thm_OAI_UniversalTensorSquare_sg31337
import Theorems.Thm_OAI_UniversalTensorSquare_sg31338
import Theorems.Thm_OAI_UniversalTensorSquare_sg31339
import Theorems.Thm_OAI_UniversalTensorSquare_sg31340
import Theorems.Thm_OAI_UniversalTensorSquare_sg31343
import Theorems.Thm_OAI_UniversalTensorSquare_sg31345
import Theorems.Thm_OAI_UniversalTensorSquare_sg31346
import Theorems.Thm_OAI_UniversalTensorSquare_sg31347
import Theorems.Thm_OAI_UniversalTensorSquare_sg31348
import Theorems.Thm_OAI_UniversalTensorSquare_sg31349
import Theorems.Thm_OAI_UniversalTensorSquare_sg31350
import Theorems.Thm_OAI_UniversalTensorSquare_sg31351
import Theorems.Thm_OAI_UniversalTensorSquare_sg31352
import Theorems.Thm_OAI_UniversalTensorSquare_sg31354
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg541
import Theorems.Thm_OAI_UniversalTensorSquare_sg5757
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg588
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg596
import Theorems.Thm_OAI_UniversalTensorSquare_sg602
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg814
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg9304
import Theorems.Thm_OAI_UniversalTensorSquare_sg9384
import Theorems.Thm_OAI_UniversalTensorSquare_sg9590
import Theorems.Thm_OAI_UniversalTensorSquare_sg97

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

lemma sg125 : RowSquare [2,2,2,1] [3,3,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg180 : RowSquare [4,1,1,1] [2,2,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1])) he) hh

lemma sg1078 : RowSquare [6,4] [4,4,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
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

lemma sg694 : RowSquare [6,2,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

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

lemma sg741 : RowSquare [3,2,1,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

lemma sg1109 : RowSquare [7,2,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg88

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

lemma sg2208 : RowSquare [6,4,2,1] [5,5,3] := by
  exact rowSquare_join (by decide) sg97 sg125

lemma sg2253 : RowSquare [7,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg236

lemma sg2305 : RowSquare [7,3,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg535

lemma sg2309 : RowSquare [7,3,1,1,1] [5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg541

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

lemma sg5079 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1109

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

lemma sg3170 : RowSquare [3,3,2,1,1,1,1,1,1,1] [5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg89 sg694

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

lemma sg5575 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg596

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

lemma sg8420 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg2626

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

lemma sg9294 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2309

lemma sg9296 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2305

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

lemma sg9983 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5079

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

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8736 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg814 sg1327

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

lemma sg8815 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg2251

lemma sg8819 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2253

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

lemma sg12630 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg4160

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

lemma sg9383 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2309

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14806 : RowSquare [9,7,2,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg741 sg5757

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

lemma sg15564 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg7812

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 76. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9383

lemma sg31326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9294

lemma sg31327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9384

lemma sg31328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9983

lemma sg31330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9296

lemma sg31331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10408

lemma sg31332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9304

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9590

lemma sg31342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2208 sg15564

lemma sg31344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3170 sg14806

lemma sg31353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5575 sg12630

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

lemma degreeTree43_598All_oai : degreeTree43_598.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31339,⟨sg31331,⟨sg31327,⟨sg31325,⟨sg31324,True.intro,True.intro⟩,⟨sg31326,True.intro,True.intro⟩⟩,⟨sg31329,⟨sg31328,True.intro,True.intro⟩,⟨sg31330,True.intro,True.intro⟩⟩⟩,⟨sg31335,⟨sg31333,⟨sg31332,True.intro,True.intro⟩,⟨sg31334,True.intro,True.intro⟩⟩,⟨sg31337,⟨sg31336,True.intro,True.intro⟩,⟨sg31338,True.intro,True.intro⟩⟩⟩⟩,⟨sg31347,⟨sg31343,⟨sg31341,⟨sg31340,True.intro,True.intro⟩,⟨sg31342,True.intro,True.intro⟩⟩,⟨sg31345,⟨sg31344,True.intro,True.intro⟩,⟨sg31346,True.intro,True.intro⟩⟩⟩,⟨sg31351,⟨sg31349,⟨sg31348,True.intro,True.intro⟩,⟨sg31350,True.intro,True.intro⟩⟩,⟨sg31353,⟨sg31352,True.intro,True.intro⟩,⟨sg31354,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_598All_oai := @OAI.UniversalTensorSquare.degreeTree43_598All_oai
