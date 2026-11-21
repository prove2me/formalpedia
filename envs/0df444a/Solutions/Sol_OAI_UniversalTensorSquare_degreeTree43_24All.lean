-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_24All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:00.526219+00:00
-- url     : https://prove2.me/submissions/66baafee-90c3-4302-8f05-a0d68183a3a1

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10182
import Theorems.Thm_OAI_UniversalTensorSquare_sg10287
import Theorems.Thm_OAI_UniversalTensorSquare_sg10601
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1687
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg23967
import Theorems.Thm_OAI_UniversalTensorSquare_sg23969
import Theorems.Thm_OAI_UniversalTensorSquare_sg23970
import Theorems.Thm_OAI_UniversalTensorSquare_sg23971
import Theorems.Thm_OAI_UniversalTensorSquare_sg23972
import Theorems.Thm_OAI_UniversalTensorSquare_sg23973
import Theorems.Thm_OAI_UniversalTensorSquare_sg23975
import Theorems.Thm_OAI_UniversalTensorSquare_sg23976
import Theorems.Thm_OAI_UniversalTensorSquare_sg23977
import Theorems.Thm_OAI_UniversalTensorSquare_sg23979
import Theorems.Thm_OAI_UniversalTensorSquare_sg23980
import Theorems.Thm_OAI_UniversalTensorSquare_sg23981
import Theorems.Thm_OAI_UniversalTensorSquare_sg23982
import Theorems.Thm_OAI_UniversalTensorSquare_sg23983
import Theorems.Thm_OAI_UniversalTensorSquare_sg23984
import Theorems.Thm_OAI_UniversalTensorSquare_sg23985
import Theorems.Thm_OAI_UniversalTensorSquare_sg23986
import Theorems.Thm_OAI_UniversalTensorSquare_sg23987
import Theorems.Thm_OAI_UniversalTensorSquare_sg23988
import Theorems.Thm_OAI_UniversalTensorSquare_sg23989
import Theorems.Thm_OAI_UniversalTensorSquare_sg23991
import Theorems.Thm_OAI_UniversalTensorSquare_sg23992
import Theorems.Thm_OAI_UniversalTensorSquare_sg23993
import Theorems.Thm_OAI_UniversalTensorSquare_sg23994
import Theorems.Thm_OAI_UniversalTensorSquare_sg23996
import Theorems.Thm_OAI_UniversalTensorSquare_sg23997
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415

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

lemma sg870 : RowSquare [4,3,2,1] [5,4,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [5,4,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [5,4,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [5,4,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [5,4,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,4,1])) he) hh

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg241 : RowSquare [2,2,1,1,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg17

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

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

lemma sg2636 : RowSquare [6,3,2,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg91 sg241

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

lemma sg8364 : RowSquare [5,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1687

lemma sg8452 : RowSquare [6,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg178 sg2636

lemma sg8504 : RowSquare [6,4,3,2,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg870 sg1327

lemma sg8528 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10167 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1327

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

lemma sg10100 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg312 sg2636

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23968 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8528 sg10100

lemma sg23974 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg8364 sg10601

lemma sg23978 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8452 sg10182

lemma sg23990 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,4,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8504 sg10167

lemma sg23995 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,4,4,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10287

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

lemma degreeTree43_24All_oai : degreeTree43_24.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23982,⟨sg23974,⟨sg23970,⟨sg23968,⟨sg23967,True.intro,True.intro⟩,⟨sg23969,True.intro,True.intro⟩⟩,⟨sg23972,⟨sg23971,True.intro,True.intro⟩,⟨sg23973,True.intro,True.intro⟩⟩⟩,⟨sg23978,⟨sg23976,⟨sg23975,True.intro,True.intro⟩,⟨sg23977,True.intro,True.intro⟩⟩,⟨sg23980,⟨sg23979,True.intro,True.intro⟩,⟨sg23981,True.intro,True.intro⟩⟩⟩⟩,⟨sg23990,⟨sg23986,⟨sg23984,⟨sg23983,True.intro,True.intro⟩,⟨sg23985,True.intro,True.intro⟩⟩,⟨sg23988,⟨sg23987,True.intro,True.intro⟩,⟨sg23989,True.intro,True.intro⟩⟩⟩,⟨sg23994,⟨sg23992,⟨sg23991,True.intro,True.intro⟩,⟨sg23993,True.intro,True.intro⟩⟩,⟨sg23996,⟨sg23995,True.intro,True.intro⟩,⟨sg23997,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_24All_oai := @OAI.UniversalTensorSquare.degreeTree43_24All_oai
