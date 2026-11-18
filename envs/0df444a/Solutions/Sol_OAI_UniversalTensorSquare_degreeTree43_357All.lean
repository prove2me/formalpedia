-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_357All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:45:17.912027+00:00
-- url     : https://prove2.me/submissions/270247d0-0f30-4119-9dd6-0855ca91720d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_356All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10867
import Theorems.Thm_OAI_UniversalTensorSquare_sg10869
import Theorems.Thm_OAI_UniversalTensorSquare_sg11767
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2596
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg28196
import Theorems.Thm_OAI_UniversalTensorSquare_sg28200
import Theorems.Thm_OAI_UniversalTensorSquare_sg28201
import Theorems.Thm_OAI_UniversalTensorSquare_sg28203
import Theorems.Thm_OAI_UniversalTensorSquare_sg28205
import Theorems.Thm_OAI_UniversalTensorSquare_sg28206
import Theorems.Thm_OAI_UniversalTensorSquare_sg28208
import Theorems.Thm_OAI_UniversalTensorSquare_sg28209
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg474
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg561
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780

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

lemma sgCert286 : solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 = -3 := by
  decide +kernel

lemma sg286 : RowSquare [3,2,2,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,2,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB286 sgT286 sgFlag286
  change solveCompact 8 (.full [5,3]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [5,3] (Equiv.refl (Fin 8)) sgB286 sgT286) sgFlag286 ≠ 0
  rw [sgCert286]
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

lemma sg4 : RowSquare [2,1] [1,1,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [1,1,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [1,1,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [1,1,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1])) he) hh

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg74 : RowSquare [3,2,1] [1,1,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [1,1,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1])) he) hh

lemma sg659 : RowSquare [5,4] [4,2,2,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg667 : RowSquare [5,4] [6,1,1,1] := by
  exact rowSquare_short 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [1,1,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1])) he) hh

lemma sg850 : RowSquare [4,3,2,1] [2,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1,1,1])) he) hh

lemma sg1079 : RowSquare [6,4] [5,2,2,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1489 : RowSquare [6,5] [6,2,2,1] := by
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

lemma sg104 : RowSquare [5,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7

lemma sg121 : RowSquare [2,2,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg19

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg145 : RowSquare [3,2,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg32

lemma sg508 : RowSquare [3,3,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg1 sg121

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg1248 : RowSquare [5,1,1,1,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg590

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

lemma sg1707 : RowSquare [5,4,2,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg286

lemma sg1709 : RowSquare [5,4,2,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg850

lemma sg1821 : RowSquare [6,4,1,1] [4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg142

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

lemma sg2188 : RowSquare [6,4,2,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg145

lemma sg2222 : RowSquare [6,5,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg561

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

lemma sg2665 : RowSquare [6,5,2,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg849

lemma sg2666 : RowSquare [6,5,2,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg850

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

lemma sg5351 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg1682

lemma sg5673 : RowSquare [6,5,2,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg508 sg474

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

lemma sg6124 : RowSquare [5,4,2,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg2596

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

lemma sg12655 : RowSquare [7,7,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1248 sg2702

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15024 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg5672

lemma sg15038 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg5673

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

lemma sg15539 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg6457

lemma sg15566 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg7812

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

lemma sg18254 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg659 sg10869

lemma sg18259 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg10867

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

lemma sg17115 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg8780

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1707 sg18259

lemma sg28195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1821 sg17115

lemma sg28197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2222 sg15539

lemma sg28198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15024

lemma sg28199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2665 sg15038

lemma sg28202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6124 sg11767

lemma sg28204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2188 sg15566

lemma sg28207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1709 sg18254

lemma sg28210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5351 sg12655

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

lemma degreeTree43_355All : degreeTree43_355.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28202,⟨sg28198,⟨sg28196,⟨sg28195,⟨sg28194,True.intro,True.intro⟩,True.intro⟩,⟨sg28197,True.intro,True.intro⟩⟩,⟨sg28200,⟨sg28199,True.intro,True.intro⟩,⟨sg28201,True.intro,True.intro⟩⟩⟩,⟨sg28206,⟨sg28204,⟨sg28203,True.intro,True.intro⟩,⟨sg28205,True.intro,True.intro⟩⟩,⟨sg28208,⟨sg28207,True.intro,True.intro⟩,⟨sg28209,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_357All_oai : degreeTree43_357.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28210,degreeTree43_355All,degreeTree43_356All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_357All_oai := @OAI.UniversalTensorSquare.degreeTree43_357All_oai
