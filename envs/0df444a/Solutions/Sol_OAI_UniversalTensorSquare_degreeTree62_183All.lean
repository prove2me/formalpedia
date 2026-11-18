-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_183All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:02:31.885964+00:00
-- url     : https://prove2.me/submissions/9d613163-24be-4685-8d5a-b424004b9b59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg1023
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg16745
import Theorems.Thm_OAI_UniversalTensorSquare_sg17301
import Theorems.Thm_OAI_UniversalTensorSquare_sg1756
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506
import Theorems.Thm_OAI_UniversalTensorSquare_sg20507
import Theorems.Thm_OAI_UniversalTensorSquare_sg20516
import Theorems.Thm_OAI_UniversalTensorSquare_sg34070
import Theorems.Thm_OAI_UniversalTensorSquare_sg34071
import Theorems.Thm_OAI_UniversalTensorSquare_sg34073
import Theorems.Thm_OAI_UniversalTensorSquare_sg34074
import Theorems.Thm_OAI_UniversalTensorSquare_sg34075
import Theorems.Thm_OAI_UniversalTensorSquare_sg34076
import Theorems.Thm_OAI_UniversalTensorSquare_sg34077
import Theorems.Thm_OAI_UniversalTensorSquare_sg34078
import Theorems.Thm_OAI_UniversalTensorSquare_sg34079
import Theorems.Thm_OAI_UniversalTensorSquare_sg34080
import Theorems.Thm_OAI_UniversalTensorSquare_sg34081
import Theorems.Thm_OAI_UniversalTensorSquare_sg34082
import Theorems.Thm_OAI_UniversalTensorSquare_sg34083
import Theorems.Thm_OAI_UniversalTensorSquare_sg34084
import Theorems.Thm_OAI_UniversalTensorSquare_sg34085
import Theorems.Thm_OAI_UniversalTensorSquare_sg34087
import Theorems.Thm_OAI_UniversalTensorSquare_sg34089
import Theorems.Thm_OAI_UniversalTensorSquare_sg390
import Theorems.Thm_OAI_UniversalTensorSquare_sg7

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

lemma sg1200 : RowSquare [4,2,2,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg181

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

lemma sg2114 : RowSquare [5,1,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg7 sg1023

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

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4933 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2114

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

lemma sg6496 : RowSquare [9,4,3,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg390 sg1200

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

lemma sg20636 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4933

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17336 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg6496

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,7,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17301

lemma sg34072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,7,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16745

lemma sg34086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17336

lemma sg34088 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,10,8,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17336

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

lemma degreeTree62_183All_oai : degreeTree62_183.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34079,⟨sg34074,⟨sg34071,⟨sg34070,⟨sg34069,True.intro,True.intro⟩,True.intro⟩,⟨sg34073,⟨sg34072,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34077,⟨sg34076,⟨sg34075,True.intro,True.intro⟩,True.intro⟩,⟨sg34078,True.intro,True.intro⟩⟩⟩,⟨sg34085,⟨sg34082,⟨sg34081,⟨sg34080,True.intro,True.intro⟩,True.intro⟩,⟨sg34084,⟨sg34083,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34088,⟨sg34087,⟨sg34086,True.intro,True.intro⟩,True.intro⟩,⟨sg34089,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_183All_oai := @OAI.UniversalTensorSquare.degreeTree62_183All_oai
