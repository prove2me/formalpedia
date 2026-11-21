-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_366All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:09:30.477613+00:00
-- url     : https://prove2.me/submissions/5ebe3fd9-010e-47ab-94e4-4c049e819feb

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10228
import Theorems.Thm_OAI_UniversalTensorSquare_sg10229
import Theorems.Thm_OAI_UniversalTensorSquare_sg11501
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg28323
import Theorems.Thm_OAI_UniversalTensorSquare_sg28324
import Theorems.Thm_OAI_UniversalTensorSquare_sg28326
import Theorems.Thm_OAI_UniversalTensorSquare_sg28329
import Theorems.Thm_OAI_UniversalTensorSquare_sg28332
import Theorems.Thm_OAI_UniversalTensorSquare_sg28333
import Theorems.Thm_OAI_UniversalTensorSquare_sg28334
import Theorems.Thm_OAI_UniversalTensorSquare_sg28335
import Theorems.Thm_OAI_UniversalTensorSquare_sg28337
import Theorems.Thm_OAI_UniversalTensorSquare_sg28338
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468
import Theorems.Thm_OAI_UniversalTensorSquare_sg8794
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9473

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

lemma sg3299 : RowSquare [5,4,3,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg521 : RowSquare [4,1,1,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg179

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

lemma sg1024 : RowSquare [6,1,1,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg132

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

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1383 : RowSquare [6,2,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg537

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6901 : RowSquare [5,4,3,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg3299

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

lemma sg9235 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1383

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

lemma sg9874 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1024 sg1754

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

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8749 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10228

lemma sg28327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6901 sg11501

lemma sg28328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9235

lemma sg28330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8652 sg9874

lemma sg28331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10229

lemma sg28336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8749 sg9473

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

lemma degreeTree43_366All_oai : degreeTree43_366.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28331,⟨sg28327,⟨sg28325,⟨sg28324,⟨sg28323,True.intro,True.intro⟩,True.intro⟩,⟨sg28326,True.intro,True.intro⟩⟩,⟨sg28329,⟨sg28328,True.intro,True.intro⟩,⟨sg28330,True.intro,True.intro⟩⟩⟩,⟨sg28335,⟨sg28333,⟨sg28332,True.intro,True.intro⟩,⟨sg28334,True.intro,True.intro⟩⟩,⟨sg28337,⟨sg28336,True.intro,True.intro⟩,⟨sg28338,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_366All_oai := @OAI.UniversalTensorSquare.degreeTree43_366All_oai
