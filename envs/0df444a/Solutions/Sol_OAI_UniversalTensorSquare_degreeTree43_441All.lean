-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_441All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:41.930975+00:00
-- url     : https://prove2.me/submissions/f294e374-2362-41ca-b8e2-0521acc1b9ee

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_439All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10364
import Theorems.Thm_OAI_UniversalTensorSquare_sg10867
import Theorems.Thm_OAI_UniversalTensorSquare_sg11531
import Theorems.Thm_OAI_UniversalTensorSquare_sg12954
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1817
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg21238
import Theorems.Thm_OAI_UniversalTensorSquare_sg21239
import Theorems.Thm_OAI_UniversalTensorSquare_sg21240
import Theorems.Thm_OAI_UniversalTensorSquare_sg29322
import Theorems.Thm_OAI_UniversalTensorSquare_sg29324
import Theorems.Thm_OAI_UniversalTensorSquare_sg29325
import Theorems.Thm_OAI_UniversalTensorSquare_sg29326
import Theorems.Thm_OAI_UniversalTensorSquare_sg29327
import Theorems.Thm_OAI_UniversalTensorSquare_sg29328
import Theorems.Thm_OAI_UniversalTensorSquare_sg29329
import Theorems.Thm_OAI_UniversalTensorSquare_sg29330
import Theorems.Thm_OAI_UniversalTensorSquare_sg29331
import Theorems.Thm_OAI_UniversalTensorSquare_sg29332
import Theorems.Thm_OAI_UniversalTensorSquare_sg29337
import Theorems.Thm_OAI_UniversalTensorSquare_sg29338
import Theorems.Thm_OAI_UniversalTensorSquare_sg29339
import Theorems.Thm_OAI_UniversalTensorSquare_sg29344
import Theorems.Thm_OAI_UniversalTensorSquare_sg29345
import Theorems.Thm_OAI_UniversalTensorSquare_sg29351
import Theorems.Thm_OAI_UniversalTensorSquare_sg29352
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg3998
import Theorems.Thm_OAI_UniversalTensorSquare_sg474
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg562
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
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

lemma sgCert296 : solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 = 6 := by
  decide +kernel

lemma sg296 : RowSquare [3,3,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB296 sgT296 sgFlag296
  change solveCompact 8 (.full [5,3]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [5,3] (Equiv.refl (Fin 8)) sgB296 sgT296) sgFlag296 ≠ 0
  rw [sgCert296]
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

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg75 : RowSquare [3,2,1] [2,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1])) he) hh

lemma sg123 : RowSquare [2,2,2,1] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg215 : RowSquare [4,3] [5,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg665 : RowSquare [5,4] [5,3,1] := by
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

lemma sg851 : RowSquare [4,3,2,1] [2,2,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1,1,1,1])) he) hh

lemma sg852 : RowSquare [4,3,2,1] [2,2,2,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1,1,1,1])) he) hh

lemma sg862 : RowSquare [4,3,2,1] [3,3,3,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [3,3,3,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [3,3,3,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [3,3,3,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [3,3,3,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,3,1])) he) hh

lemma sg1085 : RowSquare [6,4] [6,3,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1487 : RowSquare [6,5] [5,4,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1491 : RowSquare [6,5] [6,3,2] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1941 : RowSquare [7,5] [6,4,2] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
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

lemma sg121 : RowSquare [2,2,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg19

lemma sg508 : RowSquare [3,3,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg1 sg121

lemma sg571 : RowSquare [4,3,1,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg55

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

lemma sg1316 : RowSquare [5,4,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg55

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

lemma sg1717 : RowSquare [5,4,2,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg55

lemma sg1718 : RowSquare [5,4,2,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg123

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

lemma sg2181 : RowSquare [6,4,2,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg852

lemma sg2183 : RowSquare [6,4,2,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg296

lemma sg2223 : RowSquare [6,5,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg562

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

lemma sg2666 : RowSquare [6,5,2,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg850

lemma sg2668 : RowSquare [6,5,2,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg851

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

lemma sg5673 : RowSquare [6,5,2,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg508 sg474

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3513 : RowSquare [7,5,2,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg849

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

lemma sg14690 : RowSquare [5,5,2,2,2,2,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1941 sg3998

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

lemma sg15027 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1491 sg5672

lemma sg15032 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1487 sg5673

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

lemma sg15546 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1491 sg6457

lemma sg15579 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1085 sg7812

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

lemma sg18251 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg10867

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20973 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg11531

lemma sg21165 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12954

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

lemma sg17134 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1085 sg8780

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,4,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10364

lemma sg29333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1316 sg20973

lemma sg29334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1717 sg18251

lemma sg29335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg17134

lemma sg29336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2181 sg15579

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

lemma sg29340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21238

lemma sg29341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21239

lemma sg29342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg571 sg21240

lemma sg29343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1718 sg18251

lemma sg29346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15546

lemma sg29347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2668 sg15027

lemma sg29348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15032

lemma sg29349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg14690

lemma sg29350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg862 sg21165

lemma sg29353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2183 sg15579

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

lemma degreeTree43_440All : degreeTree43_440.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29338,⟨sg29330,⟨sg29326,⟨sg29324,⟨sg29323,True.intro,True.intro⟩,⟨sg29325,True.intro,True.intro⟩⟩,⟨sg29328,⟨sg29327,True.intro,True.intro⟩,⟨sg29329,True.intro,True.intro⟩⟩⟩,⟨sg29334,⟨sg29332,⟨sg29331,True.intro,True.intro⟩,⟨sg29333,True.intro,True.intro⟩⟩,⟨sg29336,⟨sg29335,True.intro,True.intro⟩,⟨sg29337,True.intro,True.intro⟩⟩⟩⟩,⟨sg29346,⟨sg29342,⟨sg29340,⟨sg29339,True.intro,True.intro⟩,⟨sg29341,True.intro,True.intro⟩⟩,⟨sg29344,⟨sg29343,True.intro,True.intro⟩,⟨sg29345,True.intro,True.intro⟩⟩⟩,⟨sg29350,⟨sg29348,⟨sg29347,True.intro,True.intro⟩,⟨sg29349,True.intro,True.intro⟩⟩,⟨sg29352,⟨sg29351,True.intro,True.intro⟩,⟨sg29353,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_441All_oai : degreeTree43_441.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29322,degreeTree43_439All,degreeTree43_440All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_441All_oai := @OAI.UniversalTensorSquare.degreeTree43_441All_oai
