-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_47All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:17:49.610311+00:00
-- url     : https://prove2.me/submissions/53488eda-4602-4ca1-8dd5-245ec6111788
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10222
import Theorems.Thm_OAI_UniversalTensorSquare_sg10227
import Theorems.Thm_OAI_UniversalTensorSquare_sg1330
import Theorems.Thm_OAI_UniversalTensorSquare_sg1379
import Theorems.Thm_OAI_UniversalTensorSquare_sg1523
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg24289
import Theorems.Thm_OAI_UniversalTensorSquare_sg24290
import Theorems.Thm_OAI_UniversalTensorSquare_sg24292
import Theorems.Thm_OAI_UniversalTensorSquare_sg24295
import Theorems.Thm_OAI_UniversalTensorSquare_sg24296
import Theorems.Thm_OAI_UniversalTensorSquare_sg24297
import Theorems.Thm_OAI_UniversalTensorSquare_sg24300
import Theorems.Thm_OAI_UniversalTensorSquare_sg24301
import Theorems.Thm_OAI_UniversalTensorSquare_sg24303
import Theorems.Thm_OAI_UniversalTensorSquare_sg24305
import Theorems.Thm_OAI_UniversalTensorSquare_sg24306
import Theorems.Thm_OAI_UniversalTensorSquare_sg24307
import Theorems.Thm_OAI_UniversalTensorSquare_sg24308
import Theorems.Thm_OAI_UniversalTensorSquare_sg24310
import Theorems.Thm_OAI_UniversalTensorSquare_sg24311
import Theorems.Thm_OAI_UniversalTensorSquare_sg24313
import Theorems.Thm_OAI_UniversalTensorSquare_sg24314
import Theorems.Thm_OAI_UniversalTensorSquare_sg24315
import Theorems.Thm_OAI_UniversalTensorSquare_sg24317
import Theorems.Thm_OAI_UniversalTensorSquare_sg24318
import Theorems.Thm_OAI_UniversalTensorSquare_sg24319
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg520
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg589
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8721
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg9759
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

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

lemma sgCert297 : solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 = -5 := by
  decide +kernel

lemma sg297 : RowSquare [3,3,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,3,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB297 sgT297 sgFlag297
  change solveCompact 8 (.full [4,4]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [4,4] (Equiv.refl (Fin 8)) sgB297 sgT297) sgFlag297 ≠ 0
  rw [sgCert297]
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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
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

lemma sg1478 : RowSquare [6,5] [3,3,3,2] := by
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

lemma sg244 : RowSquare [2,2,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg17 sg18

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

lemma sg594 : RowSquare [5,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg315

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

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

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

lemma sg2236 : RowSquare [6,5,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg297

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

lemma sg2632 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg92 sg244

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

lemma sg3874 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg373

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

lemma sg5549 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg589 sg590

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

lemma sg8185 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1523

lemma sg8244 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1379

lemma sg8424 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg2626

lemma sg8431 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg178 sg2632

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

lemma sg9189 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1379

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

lemma sg10081 : RowSquare [6,5,3,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg2626

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

lemma sg8577 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1330

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

lemma sg10845 : RowSquare [7,5,2,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg2702

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

lemma sg12618 : RowSquare [7,5,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg4160

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

lemma sg9484 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8185

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

lemma sg14500 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg5735

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

lemma sg15512 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1478 sg6457

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg8431 sg10222

lemma sg24293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15512

lemma sg24294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14500

lemma sg24298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8244 sg10845

lemma sg24299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9189

lemma sg24302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5549 sg12618

lemma sg24304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8577 sg10081

lemma sg24309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10227

lemma sg24312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9484

lemma sg24316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9759

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

lemma degreeTree43_47All_oai : degreeTree43_47.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24304,⟨sg24296,⟨sg24292,⟨sg24290,⟨sg24289,True.intro,True.intro⟩,⟨sg24291,True.intro,True.intro⟩⟩,⟨sg24294,⟨sg24293,True.intro,True.intro⟩,⟨sg24295,True.intro,True.intro⟩⟩⟩,⟨sg24300,⟨sg24298,⟨sg24297,True.intro,True.intro⟩,⟨sg24299,True.intro,True.intro⟩⟩,⟨sg24302,⟨sg24301,True.intro,True.intro⟩,⟨sg24303,True.intro,True.intro⟩⟩⟩⟩,⟨sg24312,⟨sg24308,⟨sg24306,⟨sg24305,True.intro,True.intro⟩,⟨sg24307,True.intro,True.intro⟩⟩,⟨sg24310,⟨sg24309,True.intro,True.intro⟩,⟨sg24311,True.intro,True.intro⟩⟩⟩,⟨sg24316,⟨sg24314,⟨sg24313,True.intro,True.intro⟩,⟨sg24315,True.intro,True.intro⟩⟩,⟨sg24318,⟨sg24317,True.intro,True.intro⟩,⟨sg24319,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_47All_oai := @OAI.UniversalTensorSquare.degreeTree43_47All_oai
