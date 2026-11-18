-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_635All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:54:48.13699+00:00
-- url     : https://prove2.me/submissions/c0e246c5-98af-489d-b724-028bd45b6263
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg31825
import Theorems.Thm_OAI_UniversalTensorSquare_sg31826
import Theorems.Thm_OAI_UniversalTensorSquare_sg31827
import Theorems.Thm_OAI_UniversalTensorSquare_sg31831
import Theorems.Thm_OAI_UniversalTensorSquare_sg31832
import Theorems.Thm_OAI_UniversalTensorSquare_sg31834
import Theorems.Thm_OAI_UniversalTensorSquare_sg31836
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg377
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468
import Theorems.Thm_OAI_UniversalTensorSquare_sg8794

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert67 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 = -8 := by
  decide +kernel

lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB67 sgT67 sgFlag67
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 ≠ 0
  rw [sgCert67]
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

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

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

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg576 : RowSquare [4,3,2] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg306

lemma sg644 : RowSquare [5,3,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg32

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg675 : RowSquare [6,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg676 : RowSquare [6,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg679 : RowSquare [6,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg181

lemma sg680 : RowSquare [6,1,1,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg377

lemma sg687 : RowSquare [6,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg69

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

lemma sg702 : RowSquare [6,2,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg32

lemma sg711 : RowSquare [7,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg33

lemma sg716 : RowSquare [8,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg16 sg49

lemma sg1048 : RowSquare [6,2,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg67

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

lemma sg5042 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,2,2] := by
  exact rowSquare_join (by decide) sg692 sg702

lemma sg5043 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,1] := by
  exact rowSquare_join (by decide) sg644 sg711

lemma sg5046 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [9,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg576 sg716

lemma sg5158 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,4,3] := by
  exact rowSquare_join (by decide) sg676 sg679

lemma sg5162 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,3,3] := by
  exact rowSquare_join (by decide) sg676 sg680

lemma sg5186 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg687

lemma sg5187 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,3,3] := by
  exact rowSquare_join (by decide) sg676 sg687

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

lemma sg5888 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1048

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

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

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

lemma sg10469 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,5,5,4] := by
  exact rowSquare_join (by decide) sg13 sg5158

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

lemma sg8793 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2251

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

lemma sg10548 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5186

lemma sg10549 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [10,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5187

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

lemma sg11361 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5888

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

lemma sg12698 : RowSquare [8,6,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg5735

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

lemma sg9431 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5042

lemma sg9432 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5043

lemma sg9438 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [10,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5046

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10469

lemma sg31828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9438

lemma sg31829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10548

lemma sg31830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9431

lemma sg31833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10549

lemma sg31835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9432

lemma sg31837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5162 sg12698

lemma sg31838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11361

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

lemma degreeTree43_635All_oai : degreeTree43_635.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31831,⟨sg31827,⟨sg31825,⟨sg31824,True.intro,True.intro⟩,⟨sg31826,True.intro,True.intro⟩⟩,⟨sg31829,⟨sg31828,True.intro,True.intro⟩,⟨sg31830,True.intro,True.intro⟩⟩⟩,⟨sg31835,⟨sg31833,⟨sg31832,True.intro,True.intro⟩,⟨sg31834,True.intro,True.intro⟩⟩,⟨sg31837,⟨sg31836,True.intro,True.intro⟩,⟨sg31838,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_635All_oai := @OAI.UniversalTensorSquare.degreeTree43_635All_oai
