-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_601All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:54:39.599421+00:00
-- url     : https://prove2.me/submissions/b7cb1d85-82fe-4c85-bf07-d1aab3e2f732
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg10410
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1523
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg241
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg31388
import Theorems.Thm_OAI_UniversalTensorSquare_sg31389
import Theorems.Thm_OAI_UniversalTensorSquare_sg31391
import Theorems.Thm_OAI_UniversalTensorSquare_sg31393
import Theorems.Thm_OAI_UniversalTensorSquare_sg31394
import Theorems.Thm_OAI_UniversalTensorSquare_sg31397
import Theorems.Thm_OAI_UniversalTensorSquare_sg31398
import Theorems.Thm_OAI_UniversalTensorSquare_sg31399
import Theorems.Thm_OAI_UniversalTensorSquare_sg31400
import Theorems.Thm_OAI_UniversalTensorSquare_sg31402
import Theorems.Thm_OAI_UniversalTensorSquare_sg31404
import Theorems.Thm_OAI_UniversalTensorSquare_sg31406
import Theorems.Thm_OAI_UniversalTensorSquare_sg31407
import Theorems.Thm_OAI_UniversalTensorSquare_sg31408
import Theorems.Thm_OAI_UniversalTensorSquare_sg31409
import Theorems.Thm_OAI_UniversalTensorSquare_sg31410
import Theorems.Thm_OAI_UniversalTensorSquare_sg31412
import Theorems.Thm_OAI_UniversalTensorSquare_sg31414
import Theorems.Thm_OAI_UniversalTensorSquare_sg31415
import Theorems.Thm_OAI_UniversalTensorSquare_sg31417
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg541
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg9862
import Theorems.Thm_OAI_UniversalTensorSquare_sg9982
import Theorems.Thm_OAI_UniversalTensorSquare_sg9987

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

lemma sg1109 : RowSquare [7,2,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg88

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

lemma sg1908 : RowSquare [7,3,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg373

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

lemma sg5025 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg694

lemma sg5079 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1109

lemma sg5081 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg1109

lemma sg5082 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,3] := by
  exact rowSquare_join (by decide) sg373 sg1109

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

lemma sg5852 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg373 sg1523

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

lemma sg6604 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg616 sg1523

lemma sg6605 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg1908

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

lemma sg9988 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5081

lemma sg9989 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5082

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8657 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1754

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

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

lemma sg11542 : RowSquare [8,6,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg3521

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

lemma sg11840 : RowSquare [8,6,2,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4345

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

lemma sg9389 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5025

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

lemma sg31390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9987

lemma sg31392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9982

lemma sg31395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5852 sg11840

lemma sg31396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6604 sg11542

lemma sg31401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10410

lemma sg31403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9988

lemma sg31405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9983

lemma sg31411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9862

lemma sg31413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6605 sg11542

lemma sg31416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9989

lemma sg31418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9389

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

lemma degreeTree43_601All_oai : degreeTree43_601.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31403,⟨sg31395,⟨sg31391,⟨sg31389,⟨sg31388,True.intro,True.intro⟩,⟨sg31390,True.intro,True.intro⟩⟩,⟨sg31393,⟨sg31392,True.intro,True.intro⟩,⟨sg31394,True.intro,True.intro⟩⟩⟩,⟨sg31399,⟨sg31397,⟨sg31396,True.intro,True.intro⟩,⟨sg31398,True.intro,True.intro⟩⟩,⟨sg31401,⟨sg31400,True.intro,True.intro⟩,⟨sg31402,True.intro,True.intro⟩⟩⟩⟩,⟨sg31411,⟨sg31407,⟨sg31405,⟨sg31404,True.intro,True.intro⟩,⟨sg31406,True.intro,True.intro⟩⟩,⟨sg31409,⟨sg31408,True.intro,True.intro⟩,⟨sg31410,True.intro,True.intro⟩⟩⟩,⟨sg31415,⟨sg31413,⟨sg31412,True.intro,True.intro⟩,⟨sg31414,True.intro,True.intro⟩⟩,⟨sg31417,⟨sg31416,True.intro,True.intro⟩,⟨sg31418,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_601All_oai := @OAI.UniversalTensorSquare.degreeTree43_601All_oai
