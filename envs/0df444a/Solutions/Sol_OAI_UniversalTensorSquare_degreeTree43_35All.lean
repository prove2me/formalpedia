-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_35All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:45:48.867197+00:00
-- url     : https://prove2.me/submissions/d1afbe6a-5d41-4a4e-ad78-b9c183075fe0

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10090
import Theorems.Thm_OAI_UniversalTensorSquare_sg10094
import Theorems.Thm_OAI_UniversalTensorSquare_sg10227
import Theorems.Thm_OAI_UniversalTensorSquare_sg10243
import Theorems.Thm_OAI_UniversalTensorSquare_sg10305
import Theorems.Thm_OAI_UniversalTensorSquare_sg10306
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg24128
import Theorems.Thm_OAI_UniversalTensorSquare_sg24129
import Theorems.Thm_OAI_UniversalTensorSquare_sg24130
import Theorems.Thm_OAI_UniversalTensorSquare_sg24131
import Theorems.Thm_OAI_UniversalTensorSquare_sg24132
import Theorems.Thm_OAI_UniversalTensorSquare_sg24134
import Theorems.Thm_OAI_UniversalTensorSquare_sg24136
import Theorems.Thm_OAI_UniversalTensorSquare_sg24138
import Theorems.Thm_OAI_UniversalTensorSquare_sg24139
import Theorems.Thm_OAI_UniversalTensorSquare_sg24140
import Theorems.Thm_OAI_UniversalTensorSquare_sg24143
import Theorems.Thm_OAI_UniversalTensorSquare_sg24144
import Theorems.Thm_OAI_UniversalTensorSquare_sg24145
import Theorems.Thm_OAI_UniversalTensorSquare_sg24149
import Theorems.Thm_OAI_UniversalTensorSquare_sg24150
import Theorems.Thm_OAI_UniversalTensorSquare_sg24151
import Theorems.Thm_OAI_UniversalTensorSquare_sg24152
import Theorems.Thm_OAI_UniversalTensorSquare_sg24153
import Theorems.Thm_OAI_UniversalTensorSquare_sg24154
import Theorems.Thm_OAI_UniversalTensorSquare_sg24155
import Theorems.Thm_OAI_UniversalTensorSquare_sg24157
import Theorems.Thm_OAI_UniversalTensorSquare_sg24158
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8418
import Theorems.Thm_OAI_UniversalTensorSquare_sg8423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8532

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert67 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 = -8 := by
  decide +kernel

lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB67 sgT67 sgFlag67
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB67 sgT67) sgFlag67 ≠ 0
  rw [sgCert67]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

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

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

lemma sg1433 : RowSquare [6,3,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg39 sg67

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

lemma sg2311 : RowSquare [7,3,2,1] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg178

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

lemma sg5526 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg587

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

lemma sg8536 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1330

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

lemma sg8994 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg588 sg2311

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8862 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5526

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9477 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1433

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

lemma sg24133 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10094

lemma sg24135 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg8536 sg10090

lemma sg24137 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg8994

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9477

lemma sg24142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10305

lemma sg24146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9477

lemma sg24147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10306

lemma sg24148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10243

lemma sg24156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10227

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

lemma degreeTree43_35All_oai : degreeTree43_35.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24143,⟨sg24135,⟨sg24131,⟨sg24129,⟨sg24128,True.intro,True.intro⟩,⟨sg24130,True.intro,True.intro⟩⟩,⟨sg24133,⟨sg24132,True.intro,True.intro⟩,⟨sg24134,True.intro,True.intro⟩⟩⟩,⟨sg24139,⟨sg24137,⟨sg24136,True.intro,True.intro⟩,⟨sg24138,True.intro,True.intro⟩⟩,⟨sg24141,⟨sg24140,True.intro,True.intro⟩,⟨sg24142,True.intro,True.intro⟩⟩⟩⟩,⟨sg24151,⟨sg24147,⟨sg24145,⟨sg24144,True.intro,True.intro⟩,⟨sg24146,True.intro,True.intro⟩⟩,⟨sg24149,⟨sg24148,True.intro,True.intro⟩,⟨sg24150,True.intro,True.intro⟩⟩⟩,⟨sg24155,⟨sg24153,⟨sg24152,True.intro,True.intro⟩,⟨sg24154,True.intro,True.intro⟩⟩,⟨sg24157,⟨sg24156,True.intro,True.intro⟩,⟨sg24158,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_35All_oai := @OAI.UniversalTensorSquare.degreeTree43_35All_oai
