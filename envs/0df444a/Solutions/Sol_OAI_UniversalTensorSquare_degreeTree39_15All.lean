-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_15All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:42:19.127426+00:00
-- url     : https://prove2.me/submissions/d8dcbf3f-78d1-42ab-baa3-caf3be4fac19

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21904
import Theorems.Thm_OAI_UniversalTensorSquare_sg21905
import Theorems.Thm_OAI_UniversalTensorSquare_sg21906
import Theorems.Thm_OAI_UniversalTensorSquare_sg21907
import Theorems.Thm_OAI_UniversalTensorSquare_sg21908
import Theorems.Thm_OAI_UniversalTensorSquare_sg21909
import Theorems.Thm_OAI_UniversalTensorSquare_sg21910
import Theorems.Thm_OAI_UniversalTensorSquare_sg21911
import Theorems.Thm_OAI_UniversalTensorSquare_sg21912
import Theorems.Thm_OAI_UniversalTensorSquare_sg21913
import Theorems.Thm_OAI_UniversalTensorSquare_sg21914
import Theorems.Thm_OAI_UniversalTensorSquare_sg21915
import Theorems.Thm_OAI_UniversalTensorSquare_sg21917
import Theorems.Thm_OAI_UniversalTensorSquare_sg21918
import Theorems.Thm_OAI_UniversalTensorSquare_sg21919
import Theorems.Thm_OAI_UniversalTensorSquare_sg21920
import Theorems.Thm_OAI_UniversalTensorSquare_sg21921
import Theorems.Thm_OAI_UniversalTensorSquare_sg21922
import Theorems.Thm_OAI_UniversalTensorSquare_sg21923
import Theorems.Thm_OAI_UniversalTensorSquare_sg21924
import Theorems.Thm_OAI_UniversalTensorSquare_sg21925
import Theorems.Thm_OAI_UniversalTensorSquare_sg21927
import Theorems.Thm_OAI_UniversalTensorSquare_sg21928
import Theorems.Thm_OAI_UniversalTensorSquare_sg21929
import Theorems.Thm_OAI_UniversalTensorSquare_sg21930
import Theorems.Thm_OAI_UniversalTensorSquare_sg21931
import Theorems.Thm_OAI_UniversalTensorSquare_sg3912
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg6771
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7575

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

lemma sg80 : RowSquare [3,2,1] [3,3] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,3])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,3]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,3]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3])) he) hh

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

lemma sg1686 : RowSquare [5,3,2,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg53

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

lemma sg6154 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1686

lemma sg6432 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3912

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21916 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6432 sg6771

lemma sg21926 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7575

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_15All_oai : degreeTree39_15.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21918,⟨sg21911,⟨sg21907,⟨sg21905,⟨sg21904,True.intro,True.intro⟩,⟨sg21906,True.intro,True.intro⟩⟩,⟨sg21909,⟨sg21908,True.intro,True.intro⟩,⟨sg21910,True.intro,True.intro⟩⟩⟩,⟨sg21915,⟨sg21913,⟨sg21912,True.intro,True.intro⟩,⟨sg21914,True.intro,True.intro⟩⟩,⟨sg21917,⟨sg21916,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21925,⟨sg21922,⟨sg21920,⟨sg21919,True.intro,True.intro⟩,⟨sg21921,True.intro,True.intro⟩⟩,⟨sg21924,⟨sg21923,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21929,⟨sg21927,⟨sg21926,True.intro,True.intro⟩,⟨sg21928,True.intro,True.intro⟩⟩,⟨sg21931,⟨sg21930,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_15All_oai := @OAI.UniversalTensorSquare.degreeTree39_15All_oai
