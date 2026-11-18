-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_342All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:20:46.057246+00:00
-- url     : https://prove2.me/submissions/a92fd28d-62af-4850-8c6b-6b88bb8e7fce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10217
import Theorems.Thm_OAI_UniversalTensorSquare_sg10218
import Theorems.Thm_OAI_UniversalTensorSquare_sg10219
import Theorems.Thm_OAI_UniversalTensorSquare_sg10867
import Theorems.Thm_OAI_UniversalTensorSquare_sg11531
import Theorems.Thm_OAI_UniversalTensorSquare_sg1232
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg28036
import Theorems.Thm_OAI_UniversalTensorSquare_sg28037
import Theorems.Thm_OAI_UniversalTensorSquare_sg28038
import Theorems.Thm_OAI_UniversalTensorSquare_sg28041
import Theorems.Thm_OAI_UniversalTensorSquare_sg28042
import Theorems.Thm_OAI_UniversalTensorSquare_sg28043
import Theorems.Thm_OAI_UniversalTensorSquare_sg28044
import Theorems.Thm_OAI_UniversalTensorSquare_sg28047
import Theorems.Thm_OAI_UniversalTensorSquare_sg28048
import Theorems.Thm_OAI_UniversalTensorSquare_sg28049
import Theorems.Thm_OAI_UniversalTensorSquare_sg28051
import Theorems.Thm_OAI_UniversalTensorSquare_sg28052
import Theorems.Thm_OAI_UniversalTensorSquare_sg28053
import Theorems.Thm_OAI_UniversalTensorSquare_sg28055
import Theorems.Thm_OAI_UniversalTensorSquare_sg28056
import Theorems.Thm_OAI_UniversalTensorSquare_sg28058
import Theorems.Thm_OAI_UniversalTensorSquare_sg28059
import Theorems.Thm_OAI_UniversalTensorSquare_sg28060
import Theorems.Thm_OAI_UniversalTensorSquare_sg28061
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg789
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert143

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

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg43 : RowSquare [3,2] [4,1] := by
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

lemma sg663 : RowSquare [5,4] [5,2,1,1] := by
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

lemma sg854 : RowSquare [4,3,2,1] [2,2,2,2,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,2,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,2,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,2,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2,2])) he) hh

lemma sg1076 : RowSquare [6,4] [4,2,2,2] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1083 : RowSquare [6,4] [6,2,1,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1494 : RowSquare [6,5] [7,2,1,1] := by
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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg233 : RowSquare [6,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg247 : RowSquare [2,2,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg19

lemma sg261 : RowSquare [3,1,1,1,1,1] [4,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg88

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg527 : RowSquare [4,1,1,1,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg261

lemma sg546 : RowSquare [4,2,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg4 sg53

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

lemma sg788 : RowSquare [3,3,1,1,1,1] [9,1] := by
  exact rowSquare_join (by decide) sg1 sg247

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

lemma sg1306 : RowSquare [5,4,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg143

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1460 : RowSquare [6,4,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg74

lemma sg1475 : RowSquare [6,4,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg75

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

lemma sg1713 : RowSquare [5,4,2,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg854

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

lemma sg2177 : RowSquare [6,4,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg142

lemma sg2186 : RowSquare [6,4,2,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg850

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

lemma sg5134 : RowSquare [4,3,3,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg233 sg1232

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

lemma sg3866 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg370

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

lemma sg7813 : RowSquare [6,6,2,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg788 sg789

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

lemma sg8522 : RowSquare [6,4,3,2,1,1,1,1,1,1] [8,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5134

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

lemma sg10167 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1327

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

lemma sg8680 : RowSquare [6,5,2,2,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg546 sg1754

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

lemma sg9657 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg1371

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

lemma sg14513 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg527 sg5735

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

lemma sg15036 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1494 sg5672

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

lemma sg15567 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1076 sg7813

lemma sg15576 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1083 sg7812

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

lemma sg18248 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg10867

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

lemma sg20941 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1475 sg8780

lemma sg20977 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg11531

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 68. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8680 sg9657

lemma sg28034 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8522 sg10167

lemma sg28035 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1306 sg20977

lemma sg28039 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg15567

lemma sg28040 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2665 sg15036

lemma sg28045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1713 sg18248

lemma sg28046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1460 sg20941

lemma sg28050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10217

lemma sg28054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2177 sg15576

lemma sg28057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10218

lemma sg28062 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3866 sg14513

lemma sg28063 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,4,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10219

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

lemma degreeTree43_342All_oai : degreeTree43_342.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28048,⟨sg28040,⟨sg28036,⟨sg28034,⟨sg28033,True.intro,True.intro⟩,⟨sg28035,True.intro,True.intro⟩⟩,⟨sg28038,⟨sg28037,True.intro,True.intro⟩,⟨sg28039,True.intro,True.intro⟩⟩⟩,⟨sg28044,⟨sg28042,⟨sg28041,True.intro,True.intro⟩,⟨sg28043,True.intro,True.intro⟩⟩,⟨sg28046,⟨sg28045,True.intro,True.intro⟩,⟨sg28047,True.intro,True.intro⟩⟩⟩⟩,⟨sg28056,⟨sg28052,⟨sg28050,⟨sg28049,True.intro,True.intro⟩,⟨sg28051,True.intro,True.intro⟩⟩,⟨sg28054,⟨sg28053,True.intro,True.intro⟩,⟨sg28055,True.intro,True.intro⟩⟩⟩,⟨sg28060,⟨sg28058,⟨sg28057,True.intro,True.intro⟩,⟨sg28059,True.intro,True.intro⟩⟩,⟨sg28062,⟨sg28061,True.intro,True.intro⟩,⟨sg28063,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_342All_oai := @OAI.UniversalTensorSquare.degreeTree43_342All_oai
