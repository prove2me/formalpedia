-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_248All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:00:38.833427+00:00
-- url     : https://prove2.me/submissions/e5e7daf4-59b2-4218-8a4f-e993adf1ced2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_244All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_245All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg26807
import Theorems.Thm_OAI_UniversalTensorSquare_sg26808
import Theorems.Thm_OAI_UniversalTensorSquare_sg26809
import Theorems.Thm_OAI_UniversalTensorSquare_sg26810
import Theorems.Thm_OAI_UniversalTensorSquare_sg26811
import Theorems.Thm_OAI_UniversalTensorSquare_sg26812
import Theorems.Thm_OAI_UniversalTensorSquare_sg26813
import Theorems.Thm_OAI_UniversalTensorSquare_sg26815
import Theorems.Thm_OAI_UniversalTensorSquare_sg26816
import Theorems.Thm_OAI_UniversalTensorSquare_sg26818
import Theorems.Thm_OAI_UniversalTensorSquare_sg26819
import Theorems.Thm_OAI_UniversalTensorSquare_sg26820
import Theorems.Thm_OAI_UniversalTensorSquare_sg26821
import Theorems.Thm_OAI_UniversalTensorSquare_sg26822
import Theorems.Thm_OAI_UniversalTensorSquare_sg26823
import Theorems.Thm_OAI_UniversalTensorSquare_sg26824
import Theorems.Thm_OAI_UniversalTensorSquare_sg26825
import Theorems.Thm_OAI_UniversalTensorSquare_sg26827
import Theorems.Thm_OAI_UniversalTensorSquare_sg26831
import Theorems.Thm_OAI_UniversalTensorSquare_sg26832
import Theorems.Thm_OAI_UniversalTensorSquare_sg26833
import Theorems.Thm_OAI_UniversalTensorSquare_sg26834
import Theorems.Thm_OAI_UniversalTensorSquare_sg26836
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg314
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg3521
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg4345
import Theorems.Thm_OAI_UniversalTensorSquare_sg459
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg543
import Theorems.Thm_OAI_UniversalTensorSquare_sg5672
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6002
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9132
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sg9219
import Theorems.Thm_OAI_UniversalTensorSquare_sg9220
import Theorems.Thm_OAI_UniversalTensorSquare_sg9222
import Theorems.Thm_OAI_UniversalTensorSquare_sg9836

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

lemma sg123 : RowSquare [2,2,2,1] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg1480 : RowSquare [6,5] [4,3,3,1] := by
  exact rowSquare_short 5 1 (by decide) (by decide) (by decide)
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

lemma sg134 : RowSquare [3,1,1,1,1] [3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg89

lemma sg137 : RowSquare [3,1,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg274 : RowSquare [3,2,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg33

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg137

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

lemma sg821 : RowSquare [4,2,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg459

lemma sg1004 : RowSquare [6,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

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

lemma sg1676 : RowSquare [5,2,2,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg543

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

lemma sg2688 : RowSquare [6,5,2,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg207 sg123

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4680 : RowSquare [4,4,2,1,1,1,1,1,1,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1041

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

lemma sg5414 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg910

lemma sg5525 : RowSquare [5,5,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7783 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg1754

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

lemma sg8534 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1004 sg1327

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

lemma sg10116 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1676

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8805 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg2702

lemma sg8806 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg274 sg2251

lemma sg8807 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7783

lemma sg8809 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5414

lemma sg8860 : RowSquare [7,6,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5525

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11829 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg3521

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

lemma sg12940 : RowSquare [8,6,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg821 sg4345

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15012 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [5,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1480 sg5672

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4680 sg12940

lemma sg26806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8534 sg10116

lemma sg26814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2688 sg15012

lemma sg26817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6002 sg11829

lemma sg26826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9219

lemma sg26828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9222

lemma sg26829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9220

lemma sg26830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9836

lemma sg26835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9219

lemma sg26837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9132

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

lemma degreeTree43_246All : degreeTree43_246.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26790,degreeTree43_244All,degreeTree43_245All⟩

lemma degreeTree43_247All : degreeTree43_247.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26822,⟨sg26814,⟨sg26810,⟨sg26808,⟨sg26807,True.intro,True.intro⟩,⟨sg26809,True.intro,True.intro⟩⟩,⟨sg26812,⟨sg26811,True.intro,True.intro⟩,⟨sg26813,True.intro,True.intro⟩⟩⟩,⟨sg26818,⟨sg26816,⟨sg26815,True.intro,True.intro⟩,⟨sg26817,True.intro,True.intro⟩⟩,⟨sg26820,⟨sg26819,True.intro,True.intro⟩,⟨sg26821,True.intro,True.intro⟩⟩⟩⟩,⟨sg26830,⟨sg26826,⟨sg26824,⟨sg26823,True.intro,True.intro⟩,⟨sg26825,True.intro,True.intro⟩⟩,⟨sg26828,⟨sg26827,True.intro,True.intro⟩,⟨sg26829,True.intro,True.intro⟩⟩⟩,⟨sg26834,⟨sg26832,⟨sg26831,True.intro,True.intro⟩,⟨sg26833,True.intro,True.intro⟩⟩,⟨sg26836,⟨sg26835,True.intro,True.intro⟩,⟨sg26837,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_248All_oai : degreeTree43_248.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26806,degreeTree43_246All,degreeTree43_247All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_248All_oai := @OAI.UniversalTensorSquare.degreeTree43_248All_oai
