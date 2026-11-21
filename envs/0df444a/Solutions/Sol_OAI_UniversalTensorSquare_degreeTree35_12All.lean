-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree35_12All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:02:27.518228+00:00
-- url     : https://prove2.me/submissions/488fe75b-546f-437e-915f-2631815f1d74

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_0All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_10All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_1All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_5All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_7All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_8All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg21414
import Theorems.Thm_OAI_UniversalTensorSquare_sg21447
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg186 : RowSquare [4,1,1,1] [4,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [4,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [4,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [4,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [4,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [4,1,1,1])) he) hh

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

lemma sg965 : RowSquare [5,3,1,1] [3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg67

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

lemma sg3839 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg373

lemma sg3935 : RowSquare [4,4,2,2,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1650

lemma sg3983 : RowSquare [5,4,2,1,1,1,1,1] [3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg910

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

lemma sg4785 : RowSquare [5,4,2,2,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg910

lemma sg4853 : RowSquare [6,4,2,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3983

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

lemma sg5467 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg3839

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

lemma sg5267 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg965

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

lemma sg6357 : RowSquare [6,4,2,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21365 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5467

lemma sg21381 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4853 sg5267

lemma sg21431 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3935 sg6357

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree35_2All : degreeTree35_2.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21365,degreeTree35_0All,degreeTree35_1All⟩

lemma degreeTree35_6All : degreeTree35_6.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21381,degreeTree35_2All,degreeTree35_5All⟩

lemma degreeTree35_9All : degreeTree35_9.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21431,degreeTree35_7All,degreeTree35_8All⟩

lemma degreeTree35_11All : degreeTree35_11.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21447,degreeTree35_9All,degreeTree35_10All⟩

lemma degreeTree35_12All_oai : degreeTree35_12.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21414,degreeTree35_6All,degreeTree35_11All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree35_12All_oai := @OAI.UniversalTensorSquare.degreeTree35_12All_oai
