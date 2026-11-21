-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree41_11All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:53:38.819404+00:00
-- url     : https://prove2.me/submissions/19e3daaf-5001-4cf4-a69c-817a74bf6ad8

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg23657
import Theorems.Thm_OAI_UniversalTensorSquare_sg23658
import Theorems.Thm_OAI_UniversalTensorSquare_sg23659
import Theorems.Thm_OAI_UniversalTensorSquare_sg23660
import Theorems.Thm_OAI_UniversalTensorSquare_sg23661
import Theorems.Thm_OAI_UniversalTensorSquare_sg23662
import Theorems.Thm_OAI_UniversalTensorSquare_sg23663
import Theorems.Thm_OAI_UniversalTensorSquare_sg23664
import Theorems.Thm_OAI_UniversalTensorSquare_sg23665
import Theorems.Thm_OAI_UniversalTensorSquare_sg23668
import Theorems.Thm_OAI_UniversalTensorSquare_sg23670
import Theorems.Thm_OAI_UniversalTensorSquare_sg2596
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg312
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg615
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg7

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

lemma sg26 : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

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

lemma sg316 : RowSquare [4,1,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg179

lemma sg413 : RowSquare [6,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

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

lemma sg704 : RowSquare [6,2,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg26

lemma sg716 : RowSquare [8,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg16 sg49

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

lemma sg4561 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg413 sg644

lemma sg4563 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg716

lemma sg4565 : RowSquare [3,3,2,2,1,1,1,1,1,1,1] [8,3,3,3] := by
  exact rowSquare_join (by decide) sg390 sg704

lemma sg4682 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg373 sg615

lemma sg4684 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg373 sg616

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

lemma sg7779 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg1754

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

lemma sg7790 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg316 sg1754

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

lemma sg6855 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg2596

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

lemma sg8280 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg4561

lemma sg8290 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4563

lemma sg8294 : RowSquare [5,5,2,2,1,1,1,1,1,1,1] [9,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg4565

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

lemma sg8769 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4682

lemma sg8770 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg13 sg4684

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23656 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8280

lemma sg23666 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6855 sg8769

lemma sg23667 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg8290

lemma sg23669 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6855 sg8770

lemma sg23671 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7779 sg8294

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree41_11All_oai : degreeTree41_11.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23664,⟨sg23660,⟨sg23658,⟨sg23657,⟨sg23656,True.intro,True.intro⟩,True.intro⟩,⟨sg23659,True.intro,True.intro⟩⟩,⟨sg23662,⟨sg23661,True.intro,True.intro⟩,⟨sg23663,True.intro,True.intro⟩⟩⟩,⟨sg23668,⟨sg23666,⟨sg23665,True.intro,True.intro⟩,⟨sg23667,True.intro,True.intro⟩⟩,⟨sg23670,⟨sg23669,True.intro,True.intro⟩,⟨sg23671,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree41_11All_oai := @OAI.UniversalTensorSquare.degreeTree41_11All_oai
