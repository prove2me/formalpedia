-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_445All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:16.183804+00:00
-- url     : https://prove2.me/submissions/37501b8e-ae88-4426-81a4-eadd0f6074ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1007
import Theorems.Thm_OAI_UniversalTensorSquare_sg10366
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg262
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg29355
import Theorems.Thm_OAI_UniversalTensorSquare_sg29356
import Theorems.Thm_OAI_UniversalTensorSquare_sg29358
import Theorems.Thm_OAI_UniversalTensorSquare_sg29359
import Theorems.Thm_OAI_UniversalTensorSquare_sg29360
import Theorems.Thm_OAI_UniversalTensorSquare_sg29363
import Theorems.Thm_OAI_UniversalTensorSquare_sg29364
import Theorems.Thm_OAI_UniversalTensorSquare_sg29366
import Theorems.Thm_OAI_UniversalTensorSquare_sg29367
import Theorems.Thm_OAI_UniversalTensorSquare_sg29369
import Theorems.Thm_OAI_UniversalTensorSquare_sg29370
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg4160
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg525
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg5736
import Theorems.Thm_OAI_UniversalTensorSquare_sg6914
import Theorems.Thm_OAI_UniversalTensorSquare_sg997

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

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg139 : RowSquare [3,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg0 sg52

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg528 : RowSquare [4,1,1,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg262

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3867 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg371

lemma sg3870 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg371

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

lemma sg6930 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1007

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

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

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

lemma sg11473 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg4160

lemma sg11478 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg139 sg4160

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14515 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg5735

lemma sg14519 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg5736

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 72. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6930 sg11473

lemma sg29361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14515

lemma sg29362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3867 sg14519

lemma sg29365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10366

lemma sg29368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11478

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

lemma degreeTree43_445All_oai : degreeTree43_445.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29363,⟨sg29359,⟨sg29357,⟨sg29356,⟨sg29355,True.intro,True.intro⟩,True.intro⟩,⟨sg29358,True.intro,True.intro⟩⟩,⟨sg29361,⟨sg29360,True.intro,True.intro⟩,⟨sg29362,True.intro,True.intro⟩⟩⟩,⟨sg29367,⟨sg29365,⟨sg29364,True.intro,True.intro⟩,⟨sg29366,True.intro,True.intro⟩⟩,⟨sg29369,⟨sg29368,True.intro,True.intro⟩,⟨sg29370,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_445All_oai := @OAI.UniversalTensorSquare.degreeTree43_445All_oai
