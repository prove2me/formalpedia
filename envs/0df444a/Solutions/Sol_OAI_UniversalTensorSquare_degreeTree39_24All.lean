-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_24All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:02:24.540759+00:00
-- url     : https://prove2.me/submissions/fb6d00c5-2977-4d33-ad33-0b86cc652377

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_23All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg22020
import Theorems.Thm_OAI_UniversalTensorSquare_sg22021
import Theorems.Thm_OAI_UniversalTensorSquare_sg22022
import Theorems.Thm_OAI_UniversalTensorSquare_sg22027
import Theorems.Thm_OAI_UniversalTensorSquare_sg22029
import Theorems.Thm_OAI_UniversalTensorSquare_sg22030
import Theorems.Thm_OAI_UniversalTensorSquare_sg22031
import Theorems.Thm_OAI_UniversalTensorSquare_sg22032
import Theorems.Thm_OAI_UniversalTensorSquare_sg22034
import Theorems.Thm_OAI_UniversalTensorSquare_sg22035
import Theorems.Thm_OAI_UniversalTensorSquare_sg22037
import Theorems.Thm_OAI_UniversalTensorSquare_sg22038
import Theorems.Thm_OAI_UniversalTensorSquare_sg22039
import Theorems.Thm_OAI_UniversalTensorSquare_sg22040
import Theorems.Thm_OAI_UniversalTensorSquare_sg22042
import Theorems.Thm_OAI_UniversalTensorSquare_sg22043
import Theorems.Thm_OAI_UniversalTensorSquare_sg22045
import Theorems.Thm_OAI_UniversalTensorSquare_sg22046
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6472
import Theorems.Thm_OAI_UniversalTensorSquare_sg6683
import Theorems.Thm_OAI_UniversalTensorSquare_sg6684
import Theorems.Thm_OAI_UniversalTensorSquare_sg6685
import Theorems.Thm_OAI_UniversalTensorSquare_sg6778
import Theorems.Thm_OAI_UniversalTensorSquare_sg7357
import Theorems.Thm_OAI_UniversalTensorSquare_sg7358
import Theorems.Thm_OAI_UniversalTensorSquare_sg7359
import Theorems.Thm_OAI_UniversalTensorSquare_sg7360
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

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

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

lemma sg817 : RowSquare [4,2,1,1,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg181

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

lemma sg6298 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg910

lemma sg6299 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg910

lemma sg6435 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg817

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

lemma sg22023 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7358

lemma sg22024 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6683

lemma sg22025 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7359

lemma sg22026 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6684

lemma sg22028 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7357

lemma sg22033 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7358

lemma sg22036 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7359

lemma sg22041 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7360

lemma sg22044 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6472 sg6685

lemma sg22047 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7360

lemma sg22048 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6435 sg6778

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

lemma degreeTree39_22All : degreeTree39_22.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22034,⟨sg22027,⟨sg22023,⟨sg22021,⟨sg22020,True.intro,True.intro⟩,⟨sg22022,True.intro,True.intro⟩⟩,⟨sg22025,⟨sg22024,True.intro,True.intro⟩,⟨sg22026,True.intro,True.intro⟩⟩⟩,⟨sg22031,⟨sg22029,⟨sg22028,True.intro,True.intro⟩,⟨sg22030,True.intro,True.intro⟩⟩,⟨sg22033,⟨sg22032,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22041,⟨sg22038,⟨sg22036,⟨sg22035,True.intro,True.intro⟩,⟨sg22037,True.intro,True.intro⟩⟩,⟨sg22040,⟨sg22039,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22045,⟨sg22043,⟨sg22042,True.intro,True.intro⟩,⟨sg22044,True.intro,True.intro⟩⟩,⟨sg22047,⟨sg22046,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_24All_oai : degreeTree39_24.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22048,degreeTree39_22All,degreeTree39_23All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_24All_oai := @OAI.UniversalTensorSquare.degreeTree39_24All_oai
