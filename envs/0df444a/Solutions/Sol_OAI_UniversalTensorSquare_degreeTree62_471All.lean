-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_471All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:07:12.096711+00:00
-- url     : https://prove2.me/submissions/af76360c-ea03-4251-babb-1befafe8392c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg11213
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg19330
import Theorems.Thm_OAI_UniversalTensorSquare_sg20859
import Theorems.Thm_OAI_UniversalTensorSquare_sg20860
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg37249
import Theorems.Thm_OAI_UniversalTensorSquare_sg37250
import Theorems.Thm_OAI_UniversalTensorSquare_sg37251
import Theorems.Thm_OAI_UniversalTensorSquare_sg37252
import Theorems.Thm_OAI_UniversalTensorSquare_sg37253
import Theorems.Thm_OAI_UniversalTensorSquare_sg37254
import Theorems.Thm_OAI_UniversalTensorSquare_sg37258
import Theorems.Thm_OAI_UniversalTensorSquare_sg37259
import Theorems.Thm_OAI_UniversalTensorSquare_sg37261
import Theorems.Thm_OAI_UniversalTensorSquare_sg37262
import Theorems.Thm_OAI_UniversalTensorSquare_sg37263
import Theorems.Thm_OAI_UniversalTensorSquare_sg37264
import Theorems.Thm_OAI_UniversalTensorSquare_sg37266
import Theorems.Thm_OAI_UniversalTensorSquare_sg37268
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg796
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg223 : RowSquare [5,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg270 : RowSquare [3,2,1,1,1] [2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg32

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

lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg92

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

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

lemma sg2134 : RowSquare [5,3,2,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1682

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

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

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

lemma sg3685 : RowSquare [9,2,2,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4128 : RowSquare [6,4,3,3] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg68 sg796

lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg748

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15743 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4128

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

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

lemma sg19618 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2134 sg5740

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19881 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11213

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 91. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg37255 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15743

lemma sg37256 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20860 sg15743

lemma sg37257 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19881

lemma sg37260 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19881

lemma sg37265 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19330

lemma sg37267 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,9,7,7,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19330

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

lemma degreeTree62_471All_oai : degreeTree62_471.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37259,⟨sg37254,⟨sg37251,⟨sg37250,⟨sg37249,True.intro,True.intro⟩,True.intro⟩,⟨sg37253,⟨sg37252,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37257,⟨sg37256,⟨sg37255,True.intro,True.intro⟩,True.intro⟩,⟨sg37258,True.intro,True.intro⟩⟩⟩,⟨sg37264,⟨sg37262,⟨sg37261,⟨sg37260,True.intro,True.intro⟩,True.intro⟩,⟨sg37263,True.intro,True.intro⟩⟩,⟨sg37267,⟨sg37266,⟨sg37265,True.intro,True.intro⟩,True.intro⟩,⟨sg37268,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_471All_oai := @OAI.UniversalTensorSquare.degreeTree62_471All_oai
