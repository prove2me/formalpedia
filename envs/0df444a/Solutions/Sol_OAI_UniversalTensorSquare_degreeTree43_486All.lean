-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_486All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:51:34.902188+00:00
-- url     : https://prove2.me/submissions/4536a4dd-1360-4265-86eb-2554f08170d9
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg29871
import Theorems.Thm_OAI_UniversalTensorSquare_sg29872
import Theorems.Thm_OAI_UniversalTensorSquare_sg29873
import Theorems.Thm_OAI_UniversalTensorSquare_sg29875
import Theorems.Thm_OAI_UniversalTensorSquare_sg29876
import Theorems.Thm_OAI_UniversalTensorSquare_sg29877
import Theorems.Thm_OAI_UniversalTensorSquare_sg29881
import Theorems.Thm_OAI_UniversalTensorSquare_sg29882
import Theorems.Thm_OAI_UniversalTensorSquare_sg29883
import Theorems.Thm_OAI_UniversalTensorSquare_sg29885
import Theorems.Thm_OAI_UniversalTensorSquare_sg29886
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg372
import Theorems.Thm_OAI_UniversalTensorSquare_sg6937
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg9288

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
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

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg675 : RowSquare [6,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

lemma sg692 : RowSquare [6,2,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg32

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

lemma sg807 : RowSquare [4,2,1,1,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg178

lemma sg1069 : RowSquare [6,3,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

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

lemma sg5065 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg692 sg675

lemma sg5137 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg675

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

lemma sg5806 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1069

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10353 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6937

lemma sg10355 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5137

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

lemma sg9947 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5065

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

lemma sg8720 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1327

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

lemma sg9608 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5806

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 73. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9947

lemma sg29878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9288

lemma sg29879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9608

lemma sg29880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10355

lemma sg29884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10353

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

lemma degreeTree43_486All_oai : degreeTree43_486.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29879,⟨sg29875,⟨sg29873,⟨sg29872,⟨sg29871,True.intro,True.intro⟩,True.intro⟩,⟨sg29874,True.intro,True.intro⟩⟩,⟨sg29877,⟨sg29876,True.intro,True.intro⟩,⟨sg29878,True.intro,True.intro⟩⟩⟩,⟨sg29883,⟨sg29881,⟨sg29880,True.intro,True.intro⟩,⟨sg29882,True.intro,True.intro⟩⟩,⟨sg29885,⟨sg29884,True.intro,True.intro⟩,⟨sg29886,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_486All_oai := @OAI.UniversalTensorSquare.degreeTree43_486All_oai
