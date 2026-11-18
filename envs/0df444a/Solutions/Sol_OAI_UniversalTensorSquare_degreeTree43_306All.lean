-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_306All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:47.209394+00:00
-- url     : https://prove2.me/submissions/e002a8bd-7760-4762-8bf0-304668db7eea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_302All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_305All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg27565
import Theorems.Thm_OAI_UniversalTensorSquare_sg27567
import Theorems.Thm_OAI_UniversalTensorSquare_sg27568
import Theorems.Thm_OAI_UniversalTensorSquare_sg27570
import Theorems.Thm_OAI_UniversalTensorSquare_sg27572
import Theorems.Thm_OAI_UniversalTensorSquare_sg27573
import Theorems.Thm_OAI_UniversalTensorSquare_sg27575
import Theorems.Thm_OAI_UniversalTensorSquare_sg27578
import Theorems.Thm_OAI_UniversalTensorSquare_sg27580
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg8867
import Theorems.Thm_OAI_UniversalTensorSquare_sg8884
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9755
import Theorems.Thm_OAI_UniversalTensorSquare_sg9756
import Theorems.Thm_OAI_UniversalTensorSquare_sg9759
import Theorems.Thm_OAI_UniversalTensorSquare_sg9761

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

lemma sg180 : RowSquare [4,1,1,1] [2,2,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1])) he) hh

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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg1533 : RowSquare [7,2,2] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg88

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1895 : RowSquare [7,2,2,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg180

lemma sg1900 : RowSquare [7,2,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg68

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5551 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1000

lemma sg5552 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg590 sg590

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8173 : RowSquare [5,3,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1533

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

lemma sg8991 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1895

lemma sg9065 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1900

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

lemma sg8663 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1755

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11048 : RowSquare [7,7,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5551

lemma sg11049 : RowSquare [7,7,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg13 sg5552

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 67. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9755

lemma sg27566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9756

lemma sg27569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8884 sg8991

lemma sg27571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9759

lemma sg27574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9761

lemma sg27576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,8,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8173 sg11048

lemma sg27577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8173 sg11049

lemma sg27579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8867 sg9065

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

lemma degreeTree43_303All : degreeTree43_303.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27572,⟨sg27568,⟨sg27566,⟨sg27565,True.intro,True.intro⟩,⟨sg27567,True.intro,True.intro⟩⟩,⟨sg27570,⟨sg27569,True.intro,True.intro⟩,⟨sg27571,True.intro,True.intro⟩⟩⟩,⟨sg27576,⟨sg27574,⟨sg27573,True.intro,True.intro⟩,⟨sg27575,True.intro,True.intro⟩⟩,⟨sg27578,⟨sg27577,True.intro,True.intro⟩,⟨sg27579,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_304All : degreeTree43_304.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27564,degreeTree43_302All,degreeTree43_303All⟩

lemma degreeTree43_306All_oai : degreeTree43_306.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27580,degreeTree43_304All,degreeTree43_305All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_306All_oai := @OAI.UniversalTensorSquare.degreeTree43_306All_oai
