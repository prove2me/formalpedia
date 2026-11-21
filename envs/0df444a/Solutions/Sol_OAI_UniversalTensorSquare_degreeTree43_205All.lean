-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_205All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:54:22.795933+00:00
-- url     : https://prove2.me/submissions/483ff6a7-b3ae-4840-993c-7de62e4047e4

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10297
import Theorems.Thm_OAI_UniversalTensorSquare_sg10298
import Theorems.Thm_OAI_UniversalTensorSquare_sg10315
import Theorems.Thm_OAI_UniversalTensorSquare_sg10396
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg26276
import Theorems.Thm_OAI_UniversalTensorSquare_sg26278
import Theorems.Thm_OAI_UniversalTensorSquare_sg26282
import Theorems.Thm_OAI_UniversalTensorSquare_sg26284
import Theorems.Thm_OAI_UniversalTensorSquare_sg26285
import Theorems.Thm_OAI_UniversalTensorSquare_sg26286
import Theorems.Thm_OAI_UniversalTensorSquare_sg26289
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8861
import Theorems.Thm_OAI_UniversalTensorSquare_sg9507

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

lemma sg76 : RowSquare [3,2,1] [2,2,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [2,2,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [2,2,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [2,2,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [2,2,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1])) he) hh

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

lemma sg456 : RowSquare [3,2,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg390

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

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

lemma sg811 : RowSquare [4,2,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg178

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

lemma sg1770 : RowSquare [6,2,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg456

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

lemma sg2293 : RowSquare [7,3,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg588

lemma sg2316 : RowSquare [7,3,2,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7781 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1327

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

lemma sg9048 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2316

lemma sg9206 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg2293

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

lemma sg9855 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1770

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

lemma sg8727 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg811 sg1327

lemma sg8802 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7781

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9206

lemma sg26277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9048

lemma sg26279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10396

lemma sg26280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10315

lemma sg26281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9855

lemma sg26283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10297

lemma sg26287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10298

lemma sg26288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9507

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

lemma degreeTree43_205All_oai : degreeTree43_205.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26282,⟨sg26278,⟨sg26276,⟨sg26275,True.intro,True.intro⟩,⟨sg26277,True.intro,True.intro⟩⟩,⟨sg26280,⟨sg26279,True.intro,True.intro⟩,⟨sg26281,True.intro,True.intro⟩⟩⟩,⟨sg26286,⟨sg26284,⟨sg26283,True.intro,True.intro⟩,⟨sg26285,True.intro,True.intro⟩⟩,⟨sg26288,⟨sg26287,True.intro,True.intro⟩,⟨sg26289,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_205All_oai := @OAI.UniversalTensorSquare.degreeTree43_205All_oai
