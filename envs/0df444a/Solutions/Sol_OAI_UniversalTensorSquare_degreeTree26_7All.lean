-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree26_7All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:59:36.371845+00:00
-- url     : https://prove2.me/submissions/cdaf2f49-56aa-4789-8470-eafd9df25c3f

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13039
import Theorems.Thm_OAI_UniversalTensorSquare_sg13040
import Theorems.Thm_OAI_UniversalTensorSquare_sg13041
import Theorems.Thm_OAI_UniversalTensorSquare_sg13042
import Theorems.Thm_OAI_UniversalTensorSquare_sg13043
import Theorems.Thm_OAI_UniversalTensorSquare_sg13045
import Theorems.Thm_OAI_UniversalTensorSquare_sg13046
import Theorems.Thm_OAI_UniversalTensorSquare_sg13047
import Theorems.Thm_OAI_UniversalTensorSquare_sg13048
import Theorems.Thm_OAI_UniversalTensorSquare_sg13049
import Theorems.Thm_OAI_UniversalTensorSquare_sg13051
import Theorems.Thm_OAI_UniversalTensorSquare_sg13052
import Theorems.Thm_OAI_UniversalTensorSquare_sg1638
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg4
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg636
import Theorems.Thm_OAI_UniversalTensorSquare_sg7853

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

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg211 : RowSquare [4,3] [4,1,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
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

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

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

lemma sg1149 : RowSquare [3,3,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg636

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

lemma sg2547 : RowSquare [4,4,1,1,1,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg179

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

lemma sg3274 : RowSquare [5,4,1,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg586

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

lemma sg5928 : RowSquare [4,4,2,2,2,2,2,1] [5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg1650

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11397 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7853

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13038 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg11397

lemma sg13044 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5928

lemma sg13050 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1149 sg3274

lemma sg13053 : RowSquare [8,7,2,2,2,2,2,1] [7,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1638 sg2547

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree26_7All_oai : degreeTree26_7.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13046,⟨sg13042,⟨sg13040,⟨sg13039,⟨sg13038,True.intro,True.intro⟩,True.intro⟩,⟨sg13041,True.intro,True.intro⟩⟩,⟨sg13044,⟨sg13043,True.intro,True.intro⟩,⟨sg13045,True.intro,True.intro⟩⟩⟩,⟨sg13050,⟨sg13048,⟨sg13047,True.intro,True.intro⟩,⟨sg13049,True.intro,True.intro⟩⟩,⟨sg13052,⟨sg13051,True.intro,True.intro⟩,⟨sg13053,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree26_7All_oai := @OAI.UniversalTensorSquare.degreeTree26_7All_oai
