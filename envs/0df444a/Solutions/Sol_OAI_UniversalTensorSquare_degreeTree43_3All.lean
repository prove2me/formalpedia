-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_3All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:00:43.193236+00:00
-- url     : https://prove2.me/submissions/a1881766-70b9-486a-8d00-265e4a9c0cf4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg23708
import Theorems.Thm_OAI_UniversalTensorSquare_sg23709
import Theorems.Thm_OAI_UniversalTensorSquare_sg23710
import Theorems.Thm_OAI_UniversalTensorSquare_sg23711
import Theorems.Thm_OAI_UniversalTensorSquare_sg23712
import Theorems.Thm_OAI_UniversalTensorSquare_sg23713
import Theorems.Thm_OAI_UniversalTensorSquare_sg23714
import Theorems.Thm_OAI_UniversalTensorSquare_sg23715
import Theorems.Thm_OAI_UniversalTensorSquare_sg23716
import Theorems.Thm_OAI_UniversalTensorSquare_sg23717
import Theorems.Thm_OAI_UniversalTensorSquare_sg23718
import Theorems.Thm_OAI_UniversalTensorSquare_sg23719
import Theorems.Thm_OAI_UniversalTensorSquare_sg23720
import Theorems.Thm_OAI_UniversalTensorSquare_sg23721
import Theorems.Thm_OAI_UniversalTensorSquare_sg23722
import Theorems.Thm_OAI_UniversalTensorSquare_sg23724
import Theorems.Thm_OAI_UniversalTensorSquare_sg23725
import Theorems.Thm_OAI_UniversalTensorSquare_sg23726
import Theorems.Thm_OAI_UniversalTensorSquare_sg23727
import Theorems.Thm_OAI_UniversalTensorSquare_sg23728
import Theorems.Thm_OAI_UniversalTensorSquare_sg23729
import Theorems.Thm_OAI_UniversalTensorSquare_sg23730
import Theorems.Thm_OAI_UniversalTensorSquare_sg23731
import Theorems.Thm_OAI_UniversalTensorSquare_sg23732
import Theorems.Thm_OAI_UniversalTensorSquare_sg23734
import Theorems.Thm_OAI_UniversalTensorSquare_sg23735
import Theorems.Thm_OAI_UniversalTensorSquare_sg23738
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg911

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

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

lemma sg1372 : RowSquare [6,2,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg586

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

lemma sg1874 : RowSquare [7,2,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg586

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

lemma sg2288 : RowSquare [7,3,1,1,1] [2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg586

lemma sg2290 : RowSquare [7,3,1,1,1] [3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg587

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

lemma sg6290 : RowSquare [5,5,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg911

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

lemma sg9158 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg2288

lemma sg9160 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg1874

lemma sg9161 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2290

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

lemma sg8830 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6290

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

lemma sg9693 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1331

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8798 sg9160

lemma sg23733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9693

lemma sg23736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9161

lemma sg23737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8830 sg9158

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

lemma degreeTree43_3All_oai : degreeTree43_3.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23723,⟨sg23715,⟨sg23711,⟨sg23709,⟨sg23708,True.intro,True.intro⟩,⟨sg23710,True.intro,True.intro⟩⟩,⟨sg23713,⟨sg23712,True.intro,True.intro⟩,⟨sg23714,True.intro,True.intro⟩⟩⟩,⟨sg23719,⟨sg23717,⟨sg23716,True.intro,True.intro⟩,⟨sg23718,True.intro,True.intro⟩⟩,⟨sg23721,⟨sg23720,True.intro,True.intro⟩,⟨sg23722,True.intro,True.intro⟩⟩⟩⟩,⟨sg23731,⟨sg23727,⟨sg23725,⟨sg23724,True.intro,True.intro⟩,⟨sg23726,True.intro,True.intro⟩⟩,⟨sg23729,⟨sg23728,True.intro,True.intro⟩,⟨sg23730,True.intro,True.intro⟩⟩⟩,⟨sg23735,⟨sg23733,⟨sg23732,True.intro,True.intro⟩,⟨sg23734,True.intro,True.intro⟩⟩,⟨sg23737,⟨sg23736,True.intro,True.intro⟩,⟨sg23738,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_3All_oai := @OAI.UniversalTensorSquare.degreeTree43_3All_oai
