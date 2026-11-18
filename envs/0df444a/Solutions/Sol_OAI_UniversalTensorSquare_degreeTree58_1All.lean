-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree58_1All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:42:31.566263+00:00
-- url     : https://prove2.me/submissions/a8ac93e6-5ada-426b-8f5a-3d045b357b37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg12
import Theorems.Thm_OAI_UniversalTensorSquare_sg15001
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2314
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg31979
import Theorems.Thm_OAI_UniversalTensorSquare_sg31980
import Theorems.Thm_OAI_UniversalTensorSquare_sg31981
import Theorems.Thm_OAI_UniversalTensorSquare_sg31982
import Theorems.Thm_OAI_UniversalTensorSquare_sg31983
import Theorems.Thm_OAI_UniversalTensorSquare_sg31984
import Theorems.Thm_OAI_UniversalTensorSquare_sg31985
import Theorems.Thm_OAI_UniversalTensorSquare_sg31986
import Theorems.Thm_OAI_UniversalTensorSquare_sg31987
import Theorems.Thm_OAI_UniversalTensorSquare_sg31989
import Theorems.Thm_OAI_UniversalTensorSquare_sg31990
import Theorems.Thm_OAI_UniversalTensorSquare_sg31991
import Theorems.Thm_OAI_UniversalTensorSquare_sg31992
import Theorems.Thm_OAI_UniversalTensorSquare_sg31993
import Theorems.Thm_OAI_UniversalTensorSquare_sg31994
import Theorems.Thm_OAI_UniversalTensorSquare_sg31995
import Theorems.Thm_OAI_UniversalTensorSquare_sg31996
import Theorems.Thm_OAI_UniversalTensorSquare_sg31997
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg32000
import Theorems.Thm_OAI_UniversalTensorSquare_sg32001
import Theorems.Thm_OAI_UniversalTensorSquare_sg32002
import Theorems.Thm_OAI_UniversalTensorSquare_sg32004
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg7

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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg30 : RowSquare [2,2,1] [4,1] := by
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

lemma sg193 : RowSquare [4,2,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

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

lemma sg1892 : RowSquare [7,2,2,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg178

lemma sg1923 : RowSquare [7,3,2] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg307

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

lemma sg2311 : RowSquare [7,3,2,1] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg178

lemma sg2339 : RowSquare [7,4,2] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg193

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

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

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

lemma sg3258 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1001

lemma sg3263 : RowSquare [5,3,2,1,1,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg588

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

lemma sg3522 : RowSquare [8,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg430

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

lemma sg12832 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2314

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12450 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1892 sg2339

lemma sg12451 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1923 sg2311

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

lemma sg15008 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg9 sg12451

lemma sg15010 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg12 sg12450

lemma sg15051 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg5 sg12832

lemma sg15052 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg6 sg12832

lemma sg15253 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg3263

lemma sg15257 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg3522

lemma sg15267 : RowSquare [9,7,2,2,2,1,1,1,1,1,1,1] [4,4,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg3258

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31988 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg15001

lemma sg31998 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15253 sg15051

lemma sg31999 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [13,8,7,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15253 sg15052

lemma sg32003 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,7,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15008

lemma sg32005 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,7,7,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15010

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree58_1All_oai : degreeTree58_1.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31992,⟨sg31985,⟨sg31982,⟨sg31980,⟨sg31979,True.intro,True.intro⟩,⟨sg31981,True.intro,True.intro⟩⟩,⟨sg31984,⟨sg31983,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31989,⟨sg31987,⟨sg31986,True.intro,True.intro⟩,⟨sg31988,True.intro,True.intro⟩⟩,⟨sg31991,⟨sg31990,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg31999,⟨sg31996,⟨sg31994,⟨sg31993,True.intro,True.intro⟩,⟨sg31995,True.intro,True.intro⟩⟩,⟨sg31998,⟨sg31997,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32003,⟨sg32001,⟨sg32000,True.intro,True.intro⟩,⟨sg32002,True.intro,True.intro⟩⟩,⟨sg32005,⟨sg32004,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree58_1All_oai := @OAI.UniversalTensorSquare.degreeTree58_1All_oai
