-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_148All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:51:15.396214+00:00
-- url     : https://prove2.me/submissions/bbc9bbd1-f54e-422f-8aaa-4961e5fded67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_146All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10094
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg25580
import Theorems.Thm_OAI_UniversalTensorSquare_sg25581
import Theorems.Thm_OAI_UniversalTensorSquare_sg25582
import Theorems.Thm_OAI_UniversalTensorSquare_sg25583
import Theorems.Thm_OAI_UniversalTensorSquare_sg25585
import Theorems.Thm_OAI_UniversalTensorSquare_sg25586
import Theorems.Thm_OAI_UniversalTensorSquare_sg25587
import Theorems.Thm_OAI_UniversalTensorSquare_sg25589
import Theorems.Thm_OAI_UniversalTensorSquare_sg25590
import Theorems.Thm_OAI_UniversalTensorSquare_sg25591
import Theorems.Thm_OAI_UniversalTensorSquare_sg25592
import Theorems.Thm_OAI_UniversalTensorSquare_sg25595
import Theorems.Thm_OAI_UniversalTensorSquare_sg25596
import Theorems.Thm_OAI_UniversalTensorSquare_sg25597
import Theorems.Thm_OAI_UniversalTensorSquare_sg25599
import Theorems.Thm_OAI_UniversalTensorSquare_sg25601
import Theorems.Thm_OAI_UniversalTensorSquare_sg25602
import Theorems.Thm_OAI_UniversalTensorSquare_sg25603
import Theorems.Thm_OAI_UniversalTensorSquare_sg25604
import Theorems.Thm_OAI_UniversalTensorSquare_sg25605
import Theorems.Thm_OAI_UniversalTensorSquare_sg25606
import Theorems.Thm_OAI_UniversalTensorSquare_sg25607
import Theorems.Thm_OAI_UniversalTensorSquare_sg25609
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9195

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SquareSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Columns

lemma columnShape_diagram (μ : YoungDiagram) :
    columnShape μ.transpose.rowLens = μ := by
  obtain ⟨e,hr,_⟩ := columnShape_placement μ.transpose.rowLens
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨f,hf,_⟩ := place_columns μ (List.Perm.refl _)
  rw [placed_rowLen e hr,placed_rowLen f hf]

lemma columnShape_sorted (rs : List ℕ) (hs : rs.SortedGE) (hp : ∀ a ∈ rs, 0 < a) :
    columnShape rs = (YoungDiagram.ofRowLens rs hs).transpose := by
  conv_lhs => rw [← YoungDiagram.rowLens_ofRowLens_eq_self hp (hw := hs)]
  simpa only [YoungDiagram.transpose_transpose] using
    columnShape_diagram ((YoungDiagram.ofRowLens rs hs).transpose)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sgCert17 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 = -2 := by
  decide +kernel

lemma sg17 : RowSquare [3,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB17 sgT17 sgFlag17
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 ≠ 0
  rw [sgCert17]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert315 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB315 sgT315) sgFlag315 = 24 := by
  decide +kernel

lemma sg315 : RowSquare [4,1,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB315 sgT315 sgFlag315
  change solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB315 sgT315) sgFlag315 ≠ 0
  rw [sgCert315]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert383 : solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB383 sgT383) sgFlag383 = 2 := by
  decide +kernel

lemma sg383 : RowSquare [5,1,1,1] [4,4] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB383 sgT383 sgFlag383
  change solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB383 sgT383) sgFlag383 ≠ 0
  rw [sgCert383]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert537 : solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB537 sgT537) sgFlag537 = 3 := by
  decide +kernel

lemma sg537 : RowSquare [4,2,1,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB537 sgT537 sgFlag537
  change solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB537 sgT537) sgFlag537 ≠ 0
  rw [sgCert537]
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

lemma sg5 : RowSquare [2,1] [2,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [2,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [2,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [2,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1])) he) hh

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

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg530 : RowSquare [4,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg617 : RowSquare [5,2,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg178

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

lemma sg818 : RowSquare [4,2,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg178

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1002 : RowSquare [6,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg587

lemma sg1012 : RowSquare [6,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg315

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

lemma sg1331 : RowSquare [6,1,1,1,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg530

lemma sg1383 : RowSquare [6,2,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg537

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

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

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

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

lemma sg5525 : RowSquare [5,5,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg586

lemma sg5526 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg587

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

lemma sg6288 : RowSquare [5,5,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg910

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

lemma sg8117 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg370 sg2311

lemma sg8131 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg617 sg1891

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

lemma sg9016 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg8117

lemma sg9086 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8131

lemma sg9194 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1782

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

lemma sg7232 : RowSquare [5,5,2,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg910 sg910

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

lemma sg9805 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1012 sg1757

lemma sg9806 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1383

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

lemma sg8561 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1328

lemma sg8648 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg7232

lemma sg8750 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg818 sg1327

lemma sg8752 : RowSquare [6,6,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg5525

lemma sg8798 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg6288

lemma sg8860 : RowSquare [7,6,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5525

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

lemma sg9465 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1331

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9086

lemma sg25584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8561 sg10094

lemma sg25588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9016

lemma sg25593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9805

lemma sg25594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9194

lemma sg25598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9806

lemma sg25600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9195

lemma sg25608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8750 sg9465

lemma sg25610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8752 sg9465

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

lemma degreeTree43_147All : degreeTree43_147.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25595,⟨sg25587,⟨sg25583,⟨sg25581,⟨sg25580,True.intro,True.intro⟩,⟨sg25582,True.intro,True.intro⟩⟩,⟨sg25585,⟨sg25584,True.intro,True.intro⟩,⟨sg25586,True.intro,True.intro⟩⟩⟩,⟨sg25591,⟨sg25589,⟨sg25588,True.intro,True.intro⟩,⟨sg25590,True.intro,True.intro⟩⟩,⟨sg25593,⟨sg25592,True.intro,True.intro⟩,⟨sg25594,True.intro,True.intro⟩⟩⟩⟩,⟨sg25603,⟨sg25599,⟨sg25597,⟨sg25596,True.intro,True.intro⟩,⟨sg25598,True.intro,True.intro⟩⟩,⟨sg25601,⟨sg25600,True.intro,True.intro⟩,⟨sg25602,True.intro,True.intro⟩⟩⟩,⟨sg25607,⟨sg25605,⟨sg25604,True.intro,True.intro⟩,⟨sg25606,True.intro,True.intro⟩⟩,⟨sg25609,⟨sg25608,True.intro,True.intro⟩,⟨sg25610,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_148All_oai : degreeTree43_148.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25579,degreeTree43_146All,degreeTree43_147All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_148All_oai := @OAI.UniversalTensorSquare.degreeTree43_148All_oai
