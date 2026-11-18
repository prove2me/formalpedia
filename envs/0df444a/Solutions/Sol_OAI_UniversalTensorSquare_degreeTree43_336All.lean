-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_336All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:45:13.574942+00:00
-- url     : https://prove2.me/submissions/eee1f8b4-2ece-4849-921c-d97160c07e3f
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1169
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg15686
import Theorems.Thm_OAI_UniversalTensorSquare_sg20974
import Theorems.Thm_OAI_UniversalTensorSquare_sg2105
import Theorems.Thm_OAI_UniversalTensorSquare_sg21340
import Theorems.Thm_OAI_UniversalTensorSquare_sg21342
import Theorems.Thm_OAI_UniversalTensorSquare_sg21343
import Theorems.Thm_OAI_UniversalTensorSquare_sg27940
import Theorems.Thm_OAI_UniversalTensorSquare_sg27941
import Theorems.Thm_OAI_UniversalTensorSquare_sg27942
import Theorems.Thm_OAI_UniversalTensorSquare_sg27944
import Theorems.Thm_OAI_UniversalTensorSquare_sg27946
import Theorems.Thm_OAI_UniversalTensorSquare_sg27947
import Theorems.Thm_OAI_UniversalTensorSquare_sg27948
import Theorems.Thm_OAI_UniversalTensorSquare_sg27949
import Theorems.Thm_OAI_UniversalTensorSquare_sg27950
import Theorems.Thm_OAI_UniversalTensorSquare_sg27951
import Theorems.Thm_OAI_UniversalTensorSquare_sg44
import Theorems.Thm_OAI_UniversalTensorSquare_sg561

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

lemma sgCert10 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 = -2 := by
  decide +kernel

lemma sg10 : RowSquare [2,1,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB10 sgT10 sgFlag10
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 ≠ 0
  rw [sgCert10]
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

lemma sg412 : RowSquare [5,3] [6,2] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
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

lemma sg291 : RowSquare [3,2,2,1] [3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg10

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

lemma sg1288 : RowSquare [5,3,2,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg849

lemma sg1309 : RowSquare [5,4,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg561

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

lemma sg11796 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2105

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

lemma sg21026 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg11796

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

lemma sg21341 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15686

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

lemma sg27936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg291 sg21340

lemma sg27937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg291 sg21341

lemma sg27938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg291 sg21342

lemma sg27939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg291 sg21343

lemma sg27943 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg20974

lemma sg27945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21026

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

lemma degreeTree43_336All_oai : degreeTree43_336.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27944,⟨sg27940,⟨sg27938,⟨sg27937,⟨sg27936,True.intro,True.intro⟩,True.intro⟩,⟨sg27939,True.intro,True.intro⟩⟩,⟨sg27942,⟨sg27941,True.intro,True.intro⟩,⟨sg27943,True.intro,True.intro⟩⟩⟩,⟨sg27948,⟨sg27946,⟨sg27945,True.intro,True.intro⟩,⟨sg27947,True.intro,True.intro⟩⟩,⟨sg27950,⟨sg27949,True.intro,True.intro⟩,⟨sg27951,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_336All_oai := @OAI.UniversalTensorSquare.degreeTree43_336All_oai
