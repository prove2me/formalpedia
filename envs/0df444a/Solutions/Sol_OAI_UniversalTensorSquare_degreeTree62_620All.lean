-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_620All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:55:13.640619+00:00
-- url     : https://prove2.me/submissions/11c03e9b-b3b5-44cb-b583-6288c3bb47fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg16310
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg17555
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20710
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2380
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg2633
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg3069
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg38849
import Theorems.Thm_OAI_UniversalTensorSquare_sg38850
import Theorems.Thm_OAI_UniversalTensorSquare_sg38851
import Theorems.Thm_OAI_UniversalTensorSquare_sg38852
import Theorems.Thm_OAI_UniversalTensorSquare_sg38853
import Theorems.Thm_OAI_UniversalTensorSquare_sg38856
import Theorems.Thm_OAI_UniversalTensorSquare_sg38857
import Theorems.Thm_OAI_UniversalTensorSquare_sg38858
import Theorems.Thm_OAI_UniversalTensorSquare_sg38859
import Theorems.Thm_OAI_UniversalTensorSquare_sg38860
import Theorems.Thm_OAI_UniversalTensorSquare_sg38862
import Theorems.Thm_OAI_UniversalTensorSquare_sg38863
import Theorems.Thm_OAI_UniversalTensorSquare_sg38864
import Theorems.Thm_OAI_UniversalTensorSquare_sg38865
import Theorems.Thm_OAI_UniversalTensorSquare_sg38866
import Theorems.Thm_OAI_UniversalTensorSquare_sg38867
import Theorems.Thm_OAI_UniversalTensorSquare_sg4167
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg88

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

lemma sgCert194 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 = 17 := by
  decide +kernel

lemma sg194 : RowSquare [4,2,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB194 sgT194 sgFlag194
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB194 sgT194) sgFlag194 ≠ 0
  rw [sgCert194]
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

lemma sg30 : RowSquare [2,2,1] [4,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
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

lemma sg219 : RowSquare [5,1,1] [3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg88

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

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

lemma sg1916 : RowSquare [7,3,2] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg194

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

lemma sg2214 : RowSquare [6,4,3] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg307

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

lemma sg2699 : RowSquare [7,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

lemma sg2749 : RowSquare [7,3,2,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg537

lemma sg2879 : RowSquare [8,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

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

lemma sg3120 : RowSquare [9,2,2,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg219

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

lemma sg4777 : RowSquare [5,4,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg586

lemma sg4834 : RowSquare [6,3,2,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1754

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

lemma sg13571 : RowSquare [4,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2214 sg3120

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

lemma sg12733 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4] := by
  exact rowSquare_join (by decide) sg1916 sg3069

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

lemma sg14293 : RowSquare [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,4] := by
  exact rowSquare_join (by decide) sg2380 sg2749

lemma sg14471 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg2633

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

lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4167

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

lemma sg16411 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13571

lemma sg16468 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg39 sg12733

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

lemma sg19393 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14293

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

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

lemma sg20503 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4777

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

lemma sg20686 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2699 sg4834

lemma sg20700 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14471

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38854 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16411

lemma sg38855 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16310

lemma sg38861 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16468

lemma sg38868 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19393

lemma sg38869 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17555

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

lemma degreeTree62_620All_oai : degreeTree62_620.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38859,⟨sg38854,⟨sg38851,⟨sg38850,⟨sg38849,True.intro,True.intro⟩,True.intro⟩,⟨sg38853,⟨sg38852,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38857,⟨sg38856,⟨sg38855,True.intro,True.intro⟩,True.intro⟩,⟨sg38858,True.intro,True.intro⟩⟩⟩,⟨sg38865,⟨sg38862,⟨sg38861,⟨sg38860,True.intro,True.intro⟩,True.intro⟩,⟨sg38864,⟨sg38863,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38868,⟨sg38867,⟨sg38866,True.intro,True.intro⟩,True.intro⟩,⟨sg38869,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_620All_oai := @OAI.UniversalTensorSquare.degreeTree62_620All_oai
