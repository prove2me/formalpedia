-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_255All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:09:55.362283+00:00
-- url     : https://prove2.me/submissions/0db87eb9-8930-4c25-92ee-cb5d77409597
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1522
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17323
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg202
import Theorems.Thm_OAI_UniversalTensorSquare_sg20509
import Theorems.Thm_OAI_UniversalTensorSquare_sg20510
import Theorems.Thm_OAI_UniversalTensorSquare_sg20511
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg23
import Theorems.Thm_OAI_UniversalTensorSquare_sg2341
import Theorems.Thm_OAI_UniversalTensorSquare_sg236
import Theorems.Thm_OAI_UniversalTensorSquare_sg2406
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg306
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34814
import Theorems.Thm_OAI_UniversalTensorSquare_sg34817
import Theorems.Thm_OAI_UniversalTensorSquare_sg34819
import Theorems.Thm_OAI_UniversalTensorSquare_sg34822
import Theorems.Thm_OAI_UniversalTensorSquare_sg34824
import Theorems.Thm_OAI_UniversalTensorSquare_sg34828
import Theorems.Thm_OAI_UniversalTensorSquare_sg34829
import Theorems.Thm_OAI_UniversalTensorSquare_sg34831
import Theorems.Thm_OAI_UniversalTensorSquare_sg34833
import Theorems.Thm_OAI_UniversalTensorSquare_sg451
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg615
import Theorems.Thm_OAI_UniversalTensorSquare_sg636
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg748
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg97

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

lemma sgCert195 : solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB195 sgT195) sgFlag195 = 3 := by
  decide +kernel

lemma sg195 : RowSquare [4,2,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB195 sgT195 sgFlag195
  change solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB195 sgT195) sgFlag195 ≠ 0
  rw [sgCert195]
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

lemma sg42 : RowSquare [3,2] [3,2] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg43 : RowSquare [3,2] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg560 : RowSquare [4,2,2,1] [5,4] := by
  exact rowSquare_join (by decide) sg10 sg23

lemma sg632 : RowSquare [5,2,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg23

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

lemma sg727 : RowSquare [2,2,2,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg46 sg42

lemma sg728 : RowSquare [2,2,2,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg46 sg43

lemma sg733 : RowSquare [3,1,1,1,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg20 sg92

lemma sg1145 : RowSquare [3,2,2,2,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg195

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

lemma sg2254 : RowSquare [7,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg451

lemma sg2393 : RowSquare [8,2,2,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg178

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

lemma sg2631 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg111

lemma sg2706 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg236

lemma sg2839 : RowSquare [7,4,3] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg306

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

lemma sg2928 : RowSquare [8,2,2,2] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg181

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

lemma sg3721 : RowSquare [9,3,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg586

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

lemma sg4039 : RowSquare [6,3,3,2,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1145

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

lemma sg4834 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1754

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

lemma sg5790 : RowSquare [10,4,2,2] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg615

lemma sg5791 : RowSquare [10,4,3,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg636 sg615

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6469 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg728

lemma sg6470 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg727

lemma sg6471 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg560 sg748

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

lemma sg3524 : RowSquare [8,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg733

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

lemma sg11621 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg1522 sg2406

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13549 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2393 sg2839

lemma sg13554 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg636 sg5791

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13742 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2341 sg2928

lemma sg13745 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg636 sg5790

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

lemma sg14463 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2254 sg2626

lemma sg14468 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2631

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16359 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13549

lemma sg16367 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13554

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16772 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3721 sg4039

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18911 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg6469

lemma sg18913 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6470

lemma sg18914 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg6471

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19758 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,4,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11621

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20517 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2706 sg4834

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20635 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3964

lemma sg20691 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14463

lemma sg20697 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14468

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

lemma sg17330 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13742

lemma sg17333 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13745

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 85. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34813 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19758

lemma sg34815 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19758

lemma sg34816 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19758

lemma sg34818 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19758

lemma sg34820 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19758

lemma sg34821 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17330

lemma sg34823 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17330

lemma sg34825 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16359

lemma sg34826 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17323

lemma sg34827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16772

lemma sg34830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20691 sg16367

lemma sg34832 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,11,7,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20509 sg17333

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_255All_oai : degreeTree62_255.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34823,⟨sg34818,⟨sg34815,⟨sg34814,⟨sg34813,True.intro,True.intro⟩,True.intro⟩,⟨sg34817,⟨sg34816,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34821,⟨sg34820,⟨sg34819,True.intro,True.intro⟩,True.intro⟩,⟨sg34822,True.intro,True.intro⟩⟩⟩,⟨sg34829,⟨sg34826,⟨sg34825,⟨sg34824,True.intro,True.intro⟩,True.intro⟩,⟨sg34828,⟨sg34827,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34832,⟨sg34831,⟨sg34830,True.intro,True.intro⟩,True.intro⟩,⟨sg34833,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_255All_oai := @OAI.UniversalTensorSquare.degreeTree62_255All_oai
