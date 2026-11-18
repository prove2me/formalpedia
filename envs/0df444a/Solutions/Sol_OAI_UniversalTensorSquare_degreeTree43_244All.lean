-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_244All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:37:24.485726+00:00
-- url     : https://prove2.me/submissions/24f132e8-b4e9-457c-843c-dd2bd01518f5
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg10307
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg26776
import Theorems.Thm_OAI_UniversalTensorSquare_sg26779
import Theorems.Thm_OAI_UniversalTensorSquare_sg26780
import Theorems.Thm_OAI_UniversalTensorSquare_sg26781
import Theorems.Thm_OAI_UniversalTensorSquare_sg26782
import Theorems.Thm_OAI_UniversalTensorSquare_sg26783
import Theorems.Thm_OAI_UniversalTensorSquare_sg26784
import Theorems.Thm_OAI_UniversalTensorSquare_sg26785
import Theorems.Thm_OAI_UniversalTensorSquare_sg26786
import Theorems.Thm_OAI_UniversalTensorSquare_sg26787
import Theorems.Thm_OAI_UniversalTensorSquare_sg26788
import Theorems.Thm_OAI_UniversalTensorSquare_sg4832
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780
import Theorems.Thm_OAI_UniversalTensorSquare_sg9570

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

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
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

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg123 : RowSquare [2,2,2,1] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1077 : RowSquare [6,4] [4,3,3] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1931 : RowSquare [7,5] [4,4,4] := by
  exact rowSquare_short 5 2 (by decide) (by decide) (by decide)
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

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

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

lemma sg1831 : RowSquare [6,4,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg97 sg55

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

lemma sg2199 : RowSquare [6,4,2,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg97 sg123

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

lemma sg2875 : RowSquare [7,5,1,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg142 sg207

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

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14852 : RowSquare [5,5,3,2,2,2,2,2,2,2,1,1] [5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1931 sg4832

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

lemma sg15563 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7812

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

lemma sg17109 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg8780

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9570

lemma sg26775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10307

lemma sg26777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17109

lemma sg26778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15563

lemma sg26789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2875 sg14852

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

lemma degreeTree43_244All_oai : degreeTree43_244.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26782,⟨sg26778,⟨sg26776,⟨sg26775,⟨sg26774,True.intro,True.intro⟩,True.intro⟩,⟨sg26777,True.intro,True.intro⟩⟩,⟨sg26780,⟨sg26779,True.intro,True.intro⟩,⟨sg26781,True.intro,True.intro⟩⟩⟩,⟨sg26786,⟨sg26784,⟨sg26783,True.intro,True.intro⟩,⟨sg26785,True.intro,True.intro⟩⟩,⟨sg26788,⟨sg26787,True.intro,True.intro⟩,⟨sg26789,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_244All_oai := @OAI.UniversalTensorSquare.degreeTree43_244All_oai
