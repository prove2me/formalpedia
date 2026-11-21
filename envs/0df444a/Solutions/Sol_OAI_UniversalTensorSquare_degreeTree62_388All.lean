-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_388All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:29:30.055893+00:00
-- url     : https://prove2.me/submissions/5b8a66cf-37be-4f90-986f-140a67fd5a4c

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_384All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_385All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg20859
import Theorems.Thm_OAI_UniversalTensorSquare_sg20860
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg36260
import Theorems.Thm_OAI_UniversalTensorSquare_sg36282
import Theorems.Thm_OAI_UniversalTensorSquare_sg36286
import Theorems.Thm_OAI_UniversalTensorSquare_sg36287
import Theorems.Thm_OAI_UniversalTensorSquare_sg36288
import Theorems.Thm_OAI_UniversalTensorSquare_sg36289
import Theorems.Thm_OAI_UniversalTensorSquare_sg36290
import Theorems.Thm_OAI_UniversalTensorSquare_sg36291
import Theorems.Thm_OAI_UniversalTensorSquare_sg36292
import Theorems.Thm_OAI_UniversalTensorSquare_sg36293
import Theorems.Thm_OAI_UniversalTensorSquare_sg36294
import Theorems.Thm_OAI_UniversalTensorSquare_sg36295
import Theorems.Thm_OAI_UniversalTensorSquare_sg36296
import Theorems.Thm_OAI_UniversalTensorSquare_sg36297
import Theorems.Thm_OAI_UniversalTensorSquare_sg36298
import Theorems.Thm_OAI_UniversalTensorSquare_sg36299
import Theorems.Thm_OAI_UniversalTensorSquare_sg36300
import Theorems.Thm_OAI_UniversalTensorSquare_sg36301
import Theorems.Thm_OAI_UniversalTensorSquare_sg36302
import Theorems.Thm_OAI_UniversalTensorSquare_sg36303
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg796

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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
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

lemma sg854 : RowSquare [4,3,2,1] [2,2,2,2,2] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,2,2,2,2])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,2,2,2,2]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,2,2,2,2]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,2,2,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,2,2])) he) hh

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

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

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

lemma sg2902 : RowSquare [8,2,2,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg586

lemma sg3260 : RowSquare [5,3,2,1,1,1,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg586

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

lemma sg3505 : RowSquare [7,4,3,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg854

lemma sg3522 : RowSquare [8,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg430

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

lemma sg4125 : RowSquare [6,4,3,3] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg796

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

lemma sg14821 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3505

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

lemma sg15661 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3260

lemma sg15730 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4125

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16274 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14821

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20705 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15661

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36283 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,8,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20705 sg16274

lemma sg36284 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,8,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15730

lemma sg36285 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,8,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20860 sg15730

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

lemma degreeTree62_386All : degreeTree62_386.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36293,⟨sg36288,⟨sg36285,⟨sg36284,⟨sg36283,True.intro,True.intro⟩,True.intro⟩,⟨sg36287,⟨sg36286,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36291,⟨sg36290,⟨sg36289,True.intro,True.intro⟩,True.intro⟩,⟨sg36292,True.intro,True.intro⟩⟩⟩,⟨sg36299,⟨sg36296,⟨sg36295,⟨sg36294,True.intro,True.intro⟩,True.intro⟩,⟨sg36298,⟨sg36297,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36302,⟨sg36301,⟨sg36300,True.intro,True.intro⟩,True.intro⟩,⟨sg36303,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_387All : degreeTree62_387.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36282,degreeTree62_385All,degreeTree62_386All⟩

lemma degreeTree62_388All_oai : degreeTree62_388.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36260,degreeTree62_384All,degreeTree62_387All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_388All_oai := @OAI.UniversalTensorSquare.degreeTree62_388All_oai
