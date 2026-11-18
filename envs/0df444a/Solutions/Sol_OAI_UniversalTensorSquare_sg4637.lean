-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4637
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:27:27.095643+00:00
-- url     : https://prove2.me/submissions/824f57a7-bbd6-42bf-ad14-f4ac758cca67

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
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join

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

lemma sgCert641 : solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB641 sgT641) sgFlag641 = 4 := by
  decide +kernel

lemma sg641 : RowSquare [5,2,2] [3,3,3] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB641 sgT641 sgFlag641
  change solveCompact 9 (.full [3,3,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [3,3,3] (Equiv.refl (Fin 9)) sgB641 sgT641) sgFlag641 ≠ 0
  rw [sgCert641]
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

lemma sg4637_oai : RowSquare [4,3,3,2,1,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg641

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4637_oai := @OAI.UniversalTensorSquare.sg4637_oai
