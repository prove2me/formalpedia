-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_110All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:19:41.660964+00:00
-- url     : https://prove2.me/submissions/d1386a8e-f7e6-4098-952d-df2c2ad61903

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg143
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg23328
import Theorems.Thm_OAI_UniversalTensorSquare_sg23329
import Theorems.Thm_OAI_UniversalTensorSquare_sg23330
import Theorems.Thm_OAI_UniversalTensorSquare_sg23333
import Theorems.Thm_OAI_UniversalTensorSquare_sg23334
import Theorems.Thm_OAI_UniversalTensorSquare_sg23335
import Theorems.Thm_OAI_UniversalTensorSquare_sg23336
import Theorems.Thm_OAI_UniversalTensorSquare_sg23337
import Theorems.Thm_OAI_UniversalTensorSquare_sg23338
import Theorems.Thm_OAI_UniversalTensorSquare_sg23339
import Theorems.Thm_OAI_UniversalTensorSquare_sg23340
import Theorems.Thm_OAI_UniversalTensorSquare_sg23342
import Theorems.Thm_OAI_UniversalTensorSquare_sg23343
import Theorems.Thm_OAI_UniversalTensorSquare_sg23344
import Theorems.Thm_OAI_UniversalTensorSquare_sg23345
import Theorems.Thm_OAI_UniversalTensorSquare_sg23346
import Theorems.Thm_OAI_UniversalTensorSquare_sg23347
import Theorems.Thm_OAI_UniversalTensorSquare_sg23348
import Theorems.Thm_OAI_UniversalTensorSquare_sg23349
import Theorems.Thm_OAI_UniversalTensorSquare_sg23350
import Theorems.Thm_OAI_UniversalTensorSquare_sg23353
import Theorems.Thm_OAI_UniversalTensorSquare_sg23354
import Theorems.Thm_OAI_UniversalTensorSquare_sg313
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert614

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg614 : RowSquare [5,2,1,1] [2,2,1,1,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [7,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB614 sgT614 sgFlag614
  change solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 ≠ 0
  rw [sgCert614]
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

lemma sg185 : RowSquare [4,1,1,1] [3,3,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,3,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,3,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,3,1]),
      seven_kronecker_pos _ (rowDiagram_card [3,3,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3,1])) he) hh

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

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg317 : RowSquare [4,1,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg180

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg418 : RowSquare [6,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg92

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg685 : RowSquare [6,1,1,1] [5,3,1] := by
  exact rowSquare_join (by decide) sg2 sg185

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

lemma sg1018 : RowSquare [6,1,1,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg317

lemma sg1053 : RowSquare [6,2,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg69

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

lemma sg3821 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg418

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

lemma sg5601 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg910

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

lemma sg5219 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg674

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

lemma sg6116 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg685 sg910

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

lemma sg6837 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1053

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

lemma sg6296 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg910

lemma sg6298 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg910

lemma sg6299 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg910

lemma sg6371 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg1755

lemma sg6417 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5601

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7440 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6116

lemma sg7441 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg5219

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7103 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1018

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

lemma sg7754 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3821

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23331 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6417 sg6837

lemma sg23332 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23341 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6371 sg7103

lemma sg23351 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7441

lemma sg23352 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7440

lemma sg23355 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7440

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_110All_oai : degreeTree39_110.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23342,⟨sg23335,⟨sg23331,⟨sg23329,⟨sg23328,True.intro,True.intro⟩,⟨sg23330,True.intro,True.intro⟩⟩,⟨sg23333,⟨sg23332,True.intro,True.intro⟩,⟨sg23334,True.intro,True.intro⟩⟩⟩,⟨sg23339,⟨sg23337,⟨sg23336,True.intro,True.intro⟩,⟨sg23338,True.intro,True.intro⟩⟩,⟨sg23341,⟨sg23340,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23349,⟨sg23346,⟨sg23344,⟨sg23343,True.intro,True.intro⟩,⟨sg23345,True.intro,True.intro⟩⟩,⟨sg23348,⟨sg23347,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23353,⟨sg23351,⟨sg23350,True.intro,True.intro⟩,⟨sg23352,True.intro,True.intro⟩⟩,⟨sg23355,⟨sg23354,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_110All_oai := @OAI.UniversalTensorSquare.degreeTree39_110All_oai
