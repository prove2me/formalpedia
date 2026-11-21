-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree26_32All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:06:29.481477+00:00
-- url     : https://prove2.me/submissions/b4428111-666c-4f34-bc67-9f09f0085ef0

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13254
import Theorems.Thm_OAI_UniversalTensorSquare_sg13255
import Theorems.Thm_OAI_UniversalTensorSquare_sg13256
import Theorems.Thm_OAI_UniversalTensorSquare_sg13257
import Theorems.Thm_OAI_UniversalTensorSquare_sg13258
import Theorems.Thm_OAI_UniversalTensorSquare_sg13262
import Theorems.Thm_OAI_UniversalTensorSquare_sg13264
import Theorems.Thm_OAI_UniversalTensorSquare_sg13265
import Theorems.Thm_OAI_UniversalTensorSquare_sg13266
import Theorems.Thm_OAI_UniversalTensorSquare_sg13267
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg348
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg940

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

lemma sg208 : RowSquare [4,3] [3,2,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg211 : RowSquare [4,3] [4,1,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg214 : RowSquare [4,3] [5,1,1] := by
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

lemma sg1158 : RowSquare [3,3,1,1,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg348

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

lemma sg1637 : RowSquare [4,3,1,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg940

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

lemma sg2059 : RowSquare [4,3,1,1,1,1,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg940

lemma sg2082 : RowSquare [4,4,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg66 sg178

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

lemma sg2550 : RowSquare [4,4,1,1,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg179

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

lemma sg5939 : RowSquare [4,4,2,2,2,2,2,1] [6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg1650

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

lemma sg13253 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5928

lemma sg13259 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1158 sg3274

lemma sg13260 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2059 sg2082

lemma sg13261 : RowSquare [8,7,2,2,2,2,2,1] [8,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1637 sg2550

lemma sg13263 : RowSquare [8,7,2,2,2,2,2,1] [8,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5939

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

lemma degreeTree26_32All_oai : degreeTree26_32.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13260,⟨sg13256,⟨sg13254,⟨sg13253,True.intro,True.intro⟩,⟨sg13255,True.intro,True.intro⟩⟩,⟨sg13258,⟨sg13257,True.intro,True.intro⟩,⟨sg13259,True.intro,True.intro⟩⟩⟩,⟨sg13264,⟨sg13262,⟨sg13261,True.intro,True.intro⟩,⟨sg13263,True.intro,True.intro⟩⟩,⟨sg13266,⟨sg13265,True.intro,True.intro⟩,⟨sg13267,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree26_32All_oai := @OAI.UniversalTensorSquare.degreeTree26_32All_oai
