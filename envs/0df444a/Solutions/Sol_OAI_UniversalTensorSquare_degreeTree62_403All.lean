-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_403All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:07:03.930061+00:00
-- url     : https://prove2.me/submissions/28b2e966-e282-4bf5-9f5c-db900d423452
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_397All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_402All
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18421
import Theorems.Thm_OAI_UniversalTensorSquare_sg18973
import Theorems.Thm_OAI_UniversalTensorSquare_sg19828
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg23
import Theorems.Thm_OAI_UniversalTensorSquare_sg2707
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg36414
import Theorems.Thm_OAI_UniversalTensorSquare_sg36415
import Theorems.Thm_OAI_UniversalTensorSquare_sg36416
import Theorems.Thm_OAI_UniversalTensorSquare_sg36417
import Theorems.Thm_OAI_UniversalTensorSquare_sg36418
import Theorems.Thm_OAI_UniversalTensorSquare_sg36419
import Theorems.Thm_OAI_UniversalTensorSquare_sg36420
import Theorems.Thm_OAI_UniversalTensorSquare_sg36422
import Theorems.Thm_OAI_UniversalTensorSquare_sg36425
import Theorems.Thm_OAI_UniversalTensorSquare_sg36426
import Theorems.Thm_OAI_UniversalTensorSquare_sg36428
import Theorems.Thm_OAI_UniversalTensorSquare_sg36431
import Theorems.Thm_OAI_UniversalTensorSquare_sg36433
import Theorems.Thm_OAI_UniversalTensorSquare_sg36435
import Theorems.Thm_OAI_UniversalTensorSquare_sg383
import Theorems.Thm_OAI_UniversalTensorSquare_sg44
import Theorems.Thm_OAI_UniversalTensorSquare_sg46
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg703
import Theorems.Thm_OAI_UniversalTensorSquare_sg748
import Theorems.Thm_OAI_UniversalTensorSquare_sg8892
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg11 : RowSquare [2,1,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg30 : RowSquare [2,2,1] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg42 : RowSquare [3,2] [3,2] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg330 : RowSquare [4,2,1,1] [1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [1,1,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [1,1,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1])) he) hh

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

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg455 : RowSquare [3,2,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg32

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

lemma sg729 : RowSquare [2,2,2,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg44

lemma sg888 : RowSquare [5,1,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1034 : RowSquare [6,2,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg330

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

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

lemma sg1625 : RowSquare [4,2,1,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg383

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

lemma sg1742 : RowSquare [5,4,3] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg307

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1903 : RowSquare [7,3,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg330

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

lemma sg2925 : RowSquare [8,2,2,2] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

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

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

lemma sg5741 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg1625

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

lemma sg6468 : RowSquare [7,4,3,2,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg632 sg729

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

lemma sg3580 : RowSquare [8,3,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg888

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

lemma sg8925 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1034 sg1903

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

lemma sg12856 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [7,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1742 sg2925

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

lemma sg15160 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2707 sg3580

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

lemma sg18422 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8925

lemma sg18425 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg40 sg12856

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

lemma sg18913 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6470

lemma sg18914 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg6471

lemma sg18915 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1755 sg6468

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19622 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg888 sg8892

lemma sg19665 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15160

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

lemma sg20314 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2251 sg5737

lemma sg20317 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5740

lemma sg20318 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5741

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36421 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19828

lemma sg36423 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,5,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19828

lemma sg36424 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18973

lemma sg36427 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19665

lemma sg36429 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18425

lemma sg36430 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18421

lemma sg36432 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18421

lemma sg36434 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18421

lemma sg36436 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,6,6,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18422

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

lemma degreeTree62_398All : degreeTree62_398.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36425,⟨sg36420,⟨sg36417,⟨sg36416,⟨sg36415,True.intro,True.intro⟩,True.intro⟩,⟨sg36419,⟨sg36418,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36423,⟨sg36422,⟨sg36421,True.intro,True.intro⟩,True.intro⟩,⟨sg36424,True.intro,True.intro⟩⟩⟩,⟨sg36431,⟨sg36428,⟨sg36427,⟨sg36426,True.intro,True.intro⟩,True.intro⟩,⟨sg36430,⟨sg36429,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36434,⟨sg36433,⟨sg36432,True.intro,True.intro⟩,True.intro⟩,⟨sg36435,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_399All : degreeTree62_399.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36414,degreeTree62_397All,degreeTree62_398All⟩

lemma degreeTree62_403All_oai : degreeTree62_403.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36436,degreeTree62_399All,degreeTree62_402All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_403All_oai := @OAI.UniversalTensorSquare.degreeTree62_403All_oai
