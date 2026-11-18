-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_587All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:00:56.450974+00:00
-- url     : https://prove2.me/submissions/afd825b2-8e82-4ae7-bcf7-6075bba179fa
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10403
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg1521
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg241
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg31179
import Theorems.Thm_OAI_UniversalTensorSquare_sg31180
import Theorems.Thm_OAI_UniversalTensorSquare_sg31181
import Theorems.Thm_OAI_UniversalTensorSquare_sg31183
import Theorems.Thm_OAI_UniversalTensorSquare_sg31184
import Theorems.Thm_OAI_UniversalTensorSquare_sg31186
import Theorems.Thm_OAI_UniversalTensorSquare_sg31188
import Theorems.Thm_OAI_UniversalTensorSquare_sg31190
import Theorems.Thm_OAI_UniversalTensorSquare_sg31193
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg541
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg602
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg931
import Theorems.Thm_OAI_UniversalTensorSquare_sg9845

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

lemma sgCert166 : solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 = 3 := by
  decide +kernel

lemma sg166 : RowSquare [3,3,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB166 sgT166 sgFlag166
  change solveCompact 7 (.full [5,2]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,2] (Equiv.refl (Fin 7)) sgB166 sgT166) sgFlag166 ≠ 0
  rw [sgCert166]
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

lemma sg1488 : RowSquare [6,5] [5,5,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg1520 : RowSquare [7,2,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg178

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

lemma sg2683 : RowSquare [6,5,2,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg166 sg143

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

lemma sg5845 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1520

lemma sg5846 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1521

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7249 : RowSquare [5,5,2,2,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg931

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

lemma sg8657 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1754

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

lemma sg11449 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2702

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

lemma sg15022 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg5672

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 76. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7249 sg11449

lemma sg31185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2683 sg15022

lemma sg31187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5845 sg11840

lemma sg31189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10403

lemma sg31191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8657 sg9845

lemma sg31192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5846 sg11840

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

lemma degreeTree43_587All_oai : degreeTree43_587.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31186,⟨sg31182,⟨sg31180,⟨sg31179,True.intro,True.intro⟩,⟨sg31181,True.intro,True.intro⟩⟩,⟨sg31184,⟨sg31183,True.intro,True.intro⟩,⟨sg31185,True.intro,True.intro⟩⟩⟩,⟨sg31190,⟨sg31188,⟨sg31187,True.intro,True.intro⟩,⟨sg31189,True.intro,True.intro⟩⟩,⟨sg31192,⟨sg31191,True.intro,True.intro⟩,⟨sg31193,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_587All_oai := @OAI.UniversalTensorSquare.degreeTree43_587All_oai
