-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_113All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T05:11:43.259092+00:00
-- url     : https://prove2.me/submissions/2c5fa248-0afd-481f-9f56-65dd396fcdb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg20512
import Theorems.Thm_OAI_UniversalTensorSquare_sg20515
import Theorems.Thm_OAI_UniversalTensorSquare_sg20516
import Theorems.Thm_OAI_UniversalTensorSquare_sg2314
import Theorems.Thm_OAI_UniversalTensorSquare_sg3008
import Theorems.Thm_OAI_UniversalTensorSquare_sg33301
import Theorems.Thm_OAI_UniversalTensorSquare_sg33302
import Theorems.Thm_OAI_UniversalTensorSquare_sg33303
import Theorems.Thm_OAI_UniversalTensorSquare_sg33304
import Theorems.Thm_OAI_UniversalTensorSquare_sg33305
import Theorems.Thm_OAI_UniversalTensorSquare_sg33306
import Theorems.Thm_OAI_UniversalTensorSquare_sg33307
import Theorems.Thm_OAI_UniversalTensorSquare_sg33308
import Theorems.Thm_OAI_UniversalTensorSquare_sg33309
import Theorems.Thm_OAI_UniversalTensorSquare_sg33310
import Theorems.Thm_OAI_UniversalTensorSquare_sg33311
import Theorems.Thm_OAI_UniversalTensorSquare_sg33313
import Theorems.Thm_OAI_UniversalTensorSquare_sg33315
import Theorems.Thm_OAI_UniversalTensorSquare_sg33317
import Theorems.Thm_OAI_UniversalTensorSquare_sg33319
import Theorems.Thm_OAI_UniversalTensorSquare_sg33320
import Theorems.Thm_OAI_UniversalTensorSquare_sg33321
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg2287 : RowSquare [7,3,1,1,1] [2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg910

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

lemma sg13705 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg2314 sg3008

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

lemma sg12594 : RowSquare [6,5,2,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg2287

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

lemma sg20513 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12594

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

lemma sg17274 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13705

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33312 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17274

lemma sg33314 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17274

lemma sg33316 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17274

lemma sg33318 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17274

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

lemma degreeTree62_113All_oai : degreeTree62_113.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33311,⟨sg33306,⟨sg33303,⟨sg33302,⟨sg33301,True.intro,True.intro⟩,True.intro⟩,⟨sg33305,⟨sg33304,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33309,⟨sg33308,⟨sg33307,True.intro,True.intro⟩,True.intro⟩,⟨sg33310,True.intro,True.intro⟩⟩⟩,⟨sg33317,⟨sg33314,⟨sg33313,⟨sg33312,True.intro,True.intro⟩,True.intro⟩,⟨sg33316,⟨sg33315,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33320,⟨sg33319,⟨sg33318,True.intro,True.intro⟩,True.intro⟩,⟨sg33321,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_113All_oai := @OAI.UniversalTensorSquare.degreeTree62_113All_oai
