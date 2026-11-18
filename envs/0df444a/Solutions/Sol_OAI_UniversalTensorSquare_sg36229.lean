-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36229
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T05:52:08.594118+00:00
-- url     : https://prove2.me/submissions/8fb43db0-c1d1-4e7d-844c-099f299c63d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_Columns_contractionInteger_compact
import Theorems.Thm_OAI_Saxl_Columns_polytabloid_placed_expansion
import Theorems.Thm_OAI_Saxl_intertwiningLiftSubrep_injective
import Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
import Theorems.Thm_OAI_Saxl_orbitAverage_base
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate0
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate10
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate2
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate4
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate5
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate7
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate8
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive0
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive1
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive10
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive11
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive2
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive3
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive4
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive5
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive6
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive7
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive8
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive9
import Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowLens_mem_partitionLists
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg4167
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg748
import Theorems.Thm_OAI_UniversalTensorSquare_sg87
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert17

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

lemma sg330 : RowSquare [4,2,1,1] [1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [1,1,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [1,1,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1])) he) hh

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

lemma sg2310 : RowSquare [7,3,2,1] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg330

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3000 : RowSquare [8,3,2,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg330

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13652 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2310 sg3000

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14770 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4167

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

lemma sg17168 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13652

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

lemma sg20540 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg14770

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36229_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,7,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20540 sg17168

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36229_oai := @OAI.UniversalTensorSquare.sg36229_oai
