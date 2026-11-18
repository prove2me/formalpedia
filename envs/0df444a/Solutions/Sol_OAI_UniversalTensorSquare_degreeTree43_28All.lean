-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_28All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:43:09.819849+00:00
-- url     : https://prove2.me/submissions/ba50deea-85fa-488f-8250-7475bc8990ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_27All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10211
import Theorems.Thm_OAI_UniversalTensorSquare_sg10214
import Theorems.Thm_OAI_UniversalTensorSquare_sg10215
import Theorems.Thm_OAI_UniversalTensorSquare_sg10236
import Theorems.Thm_OAI_UniversalTensorSquare_sg10291
import Theorems.Thm_OAI_UniversalTensorSquare_sg10292
import Theorems.Thm_OAI_UniversalTensorSquare_sg10293
import Theorems.Thm_OAI_UniversalTensorSquare_sg10294
import Theorems.Thm_OAI_UniversalTensorSquare_sg10295
import Theorems.Thm_OAI_UniversalTensorSquare_sg10296
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg23999
import Theorems.Thm_OAI_UniversalTensorSquare_sg24000
import Theorems.Thm_OAI_UniversalTensorSquare_sg24001
import Theorems.Thm_OAI_UniversalTensorSquare_sg24002
import Theorems.Thm_OAI_UniversalTensorSquare_sg24004
import Theorems.Thm_OAI_UniversalTensorSquare_sg24005
import Theorems.Thm_OAI_UniversalTensorSquare_sg24006
import Theorems.Thm_OAI_UniversalTensorSquare_sg24007
import Theorems.Thm_OAI_UniversalTensorSquare_sg24008
import Theorems.Thm_OAI_UniversalTensorSquare_sg24010
import Theorems.Thm_OAI_UniversalTensorSquare_sg24011
import Theorems.Thm_OAI_UniversalTensorSquare_sg24013
import Theorems.Thm_OAI_UniversalTensorSquare_sg24014
import Theorems.Thm_OAI_UniversalTensorSquare_sg24016
import Theorems.Thm_OAI_UniversalTensorSquare_sg24017
import Theorems.Thm_OAI_UniversalTensorSquare_sg24019
import Theorems.Thm_OAI_UniversalTensorSquare_sg24021
import Theorems.Thm_OAI_UniversalTensorSquare_sg24022
import Theorems.Thm_OAI_UniversalTensorSquare_sg24024
import Theorems.Thm_OAI_UniversalTensorSquare_sg24025
import Theorems.Thm_OAI_UniversalTensorSquare_sg24029
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423

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

lemma sg849 : RowSquare [4,3,2,1] [1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [1,1,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

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

lemma sg1328 : RowSquare [6,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg112

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

lemma sg8419 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg849 sg1328

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

lemma sg24003 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,4,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10211

lemma sg24009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10291

lemma sg24012 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10292

lemma sg24015 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10293

lemma sg24018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10214

lemma sg24020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10215

lemma sg24023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10294

lemma sg24026 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10295

lemma sg24027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10236

lemma sg24028 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8419 sg10236

lemma sg24030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,5,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10296

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

lemma degreeTree43_26All : degreeTree43_26.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24014,⟨sg24006,⟨sg24002,⟨sg24000,⟨sg23999,True.intro,True.intro⟩,⟨sg24001,True.intro,True.intro⟩⟩,⟨sg24004,⟨sg24003,True.intro,True.intro⟩,⟨sg24005,True.intro,True.intro⟩⟩⟩,⟨sg24010,⟨sg24008,⟨sg24007,True.intro,True.intro⟩,⟨sg24009,True.intro,True.intro⟩⟩,⟨sg24012,⟨sg24011,True.intro,True.intro⟩,⟨sg24013,True.intro,True.intro⟩⟩⟩⟩,⟨sg24022,⟨sg24018,⟨sg24016,⟨sg24015,True.intro,True.intro⟩,⟨sg24017,True.intro,True.intro⟩⟩,⟨sg24020,⟨sg24019,True.intro,True.intro⟩,⟨sg24021,True.intro,True.intro⟩⟩⟩,⟨sg24026,⟨sg24024,⟨sg24023,True.intro,True.intro⟩,⟨sg24025,True.intro,True.intro⟩⟩,⟨sg24028,⟨sg24027,True.intro,True.intro⟩,⟨sg24029,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_28All_oai : degreeTree43_28.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24030,degreeTree43_26All,degreeTree43_27All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_28All_oai := @OAI.UniversalTensorSquare.degreeTree43_28All_oai
