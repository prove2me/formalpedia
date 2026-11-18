-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_609All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:59.136218+00:00
-- url     : https://prove2.me/submissions/a7759e43-5470-475d-b6b2-83e769301ce0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg31453
import Theorems.Thm_OAI_UniversalTensorSquare_sg31455
import Theorems.Thm_OAI_UniversalTensorSquare_sg31458
import Theorems.Thm_OAI_UniversalTensorSquare_sg31459
import Theorems.Thm_OAI_UniversalTensorSquare_sg31460
import Theorems.Thm_OAI_UniversalTensorSquare_sg31461
import Theorems.Thm_OAI_UniversalTensorSquare_sg31462
import Theorems.Thm_OAI_UniversalTensorSquare_sg31463
import Theorems.Thm_OAI_UniversalTensorSquare_sg31464
import Theorems.Thm_OAI_UniversalTensorSquare_sg31465
import Theorems.Thm_OAI_UniversalTensorSquare_sg31467
import Theorems.Thm_OAI_UniversalTensorSquare_sg31468
import Theorems.Thm_OAI_UniversalTensorSquare_sg31469
import Theorems.Thm_OAI_UniversalTensorSquare_sg31470
import Theorems.Thm_OAI_UniversalTensorSquare_sg31471
import Theorems.Thm_OAI_UniversalTensorSquare_sg31472
import Theorems.Thm_OAI_UniversalTensorSquare_sg31474
import Theorems.Thm_OAI_UniversalTensorSquare_sg31475
import Theorems.Thm_OAI_UniversalTensorSquare_sg31476
import Theorems.Thm_OAI_UniversalTensorSquare_sg31477
import Theorems.Thm_OAI_UniversalTensorSquare_sg31478
import Theorems.Thm_OAI_UniversalTensorSquare_sg31479
import Theorems.Thm_OAI_UniversalTensorSquare_sg31480
import Theorems.Thm_OAI_UniversalTensorSquare_sg31483
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9108
import Theorems.Thm_OAI_UniversalTensorSquare_sg9256
import Theorems.Thm_OAI_UniversalTensorSquare_sg9349
import Theorems.Thm_OAI_UniversalTensorSquare_sg9648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9997

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

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg263 : RowSquare [3,1,1,1,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg33

lemma sg272 : RowSquare [3,2,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg74

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg531 : RowSquare [4,1,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg263

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

lemma sg1393 : RowSquare [6,2,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg271

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

lemma sg3875 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg373

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

lemma sg6391 : RowSquare [6,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg1327

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

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

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

lemma sg9327 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1393

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

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8795 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg272 sg2251

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

lemma sg8827 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg2702

lemma sg8872 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6391

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

lemma sg14521 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg531 sg5735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14521

lemma sg31456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8827 sg9256

lemma sg31457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9327

lemma sg31466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9108

lemma sg31473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9648

lemma sg31481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9349

lemma sg31482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9997

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

lemma degreeTree43_609All_oai : degreeTree43_609.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31468,⟨sg31460,⟨sg31456,⟨sg31454,⟨sg31453,True.intro,True.intro⟩,⟨sg31455,True.intro,True.intro⟩⟩,⟨sg31458,⟨sg31457,True.intro,True.intro⟩,⟨sg31459,True.intro,True.intro⟩⟩⟩,⟨sg31464,⟨sg31462,⟨sg31461,True.intro,True.intro⟩,⟨sg31463,True.intro,True.intro⟩⟩,⟨sg31466,⟨sg31465,True.intro,True.intro⟩,⟨sg31467,True.intro,True.intro⟩⟩⟩⟩,⟨sg31476,⟨sg31472,⟨sg31470,⟨sg31469,True.intro,True.intro⟩,⟨sg31471,True.intro,True.intro⟩⟩,⟨sg31474,⟨sg31473,True.intro,True.intro⟩,⟨sg31475,True.intro,True.intro⟩⟩⟩,⟨sg31480,⟨sg31478,⟨sg31477,True.intro,True.intro⟩,⟨sg31479,True.intro,True.intro⟩⟩,⟨sg31482,⟨sg31481,True.intro,True.intro⟩,⟨sg31483,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_609All_oai := @OAI.UniversalTensorSquare.degreeTree43_609All_oai
