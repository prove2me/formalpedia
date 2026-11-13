-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_154All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:51:17.792216+00:00
-- url     : https://prove2.me/submissions/d7eaaafb-0cd5-4556-a635-0a9a722d930f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_152All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10260
import Theorems.Thm_OAI_UniversalTensorSquare_sg10287
import Theorems.Thm_OAI_UniversalTensorSquare_sg10288
import Theorems.Thm_OAI_UniversalTensorSquare_sg10364
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg25644
import Theorems.Thm_OAI_UniversalTensorSquare_sg25645
import Theorems.Thm_OAI_UniversalTensorSquare_sg25646
import Theorems.Thm_OAI_UniversalTensorSquare_sg25647
import Theorems.Thm_OAI_UniversalTensorSquare_sg25648
import Theorems.Thm_OAI_UniversalTensorSquare_sg25649
import Theorems.Thm_OAI_UniversalTensorSquare_sg25650
import Theorems.Thm_OAI_UniversalTensorSquare_sg25651
import Theorems.Thm_OAI_UniversalTensorSquare_sg25653
import Theorems.Thm_OAI_UniversalTensorSquare_sg25654
import Theorems.Thm_OAI_UniversalTensorSquare_sg25655
import Theorems.Thm_OAI_UniversalTensorSquare_sg25656
import Theorems.Thm_OAI_UniversalTensorSquare_sg25657
import Theorems.Thm_OAI_UniversalTensorSquare_sg25658
import Theorems.Thm_OAI_UniversalTensorSquare_sg25659
import Theorems.Thm_OAI_UniversalTensorSquare_sg25660
import Theorems.Thm_OAI_UniversalTensorSquare_sg25661
import Theorems.Thm_OAI_UniversalTensorSquare_sg25662
import Theorems.Thm_OAI_UniversalTensorSquare_sg25663
import Theorems.Thm_OAI_UniversalTensorSquare_sg25664
import Theorems.Thm_OAI_UniversalTensorSquare_sg25665
import Theorems.Thm_OAI_UniversalTensorSquare_sg25667
import Theorems.Thm_OAI_UniversalTensorSquare_sg25671
import Theorems.Thm_OAI_UniversalTensorSquare_sg25674
import Theorems.Thm_OAI_UniversalTensorSquare_sg25675
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sgCert89 : solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB89 sgT89) sgFlag89 = 6 := by
  decide +kernel

lemma sg89 : RowSquare [4,1,1] [2,2,2] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB89 sgT89 sgFlag89
  change solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB89 sgT89) sgFlag89 ≠ 0
  rw [sgCert89]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert313 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 = 24 := by
  decide +kernel

lemma sg313 : RowSquare [4,1,1,1,1] [2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [6,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB313 sgT313 sgFlag313
  change solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 ≠ 0
  rw [sgCert313]
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

lemma sgCert373 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 = 24 := by
  decide +kernel

lemma sg373 : RowSquare [5,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB373 sgT373 sgFlag373
  change solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 ≠ 0
  rw [sgCert373]
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

lemma sg850 : RowSquare [4,3,2,1] [2,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,3,2,1] = (staircase 4) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,3,2,1]) (rowDiagram [2,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 4) (rowDiagram [2,1,1,1,1,1,1,1,1]) :=
    ⟨10,canonicalTableau _ (staircase_card 4),canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 4 (by decide) _ (rowDiagram_card [2,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg373

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

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

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

lemma sg1338 : RowSquare [6,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg262

lemma sg1348 : RowSquare [6,1,1,1,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg520

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1373 : RowSquare [6,2,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg912

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

lemma sg1883 : RowSquare [7,2,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg313

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

lemma sg8246 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1883

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1327

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1327

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

lemma sg9812 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1348

lemma sg9813 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8246

lemma sg9814 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1373 sg1338

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

lemma sg8648 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg7232

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

lemma sg25652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10260

lemma sg25666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9812

lemma sg25668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10364

lemma sg25669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10287

lemma sg25670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9813

lemma sg25672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10288

lemma sg25673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9814

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

lemma degreeTree43_153All : degreeTree43_153.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25660,⟨sg25652,⟨sg25648,⟨sg25646,⟨sg25645,True.intro,True.intro⟩,⟨sg25647,True.intro,True.intro⟩⟩,⟨sg25650,⟨sg25649,True.intro,True.intro⟩,⟨sg25651,True.intro,True.intro⟩⟩⟩,⟨sg25656,⟨sg25654,⟨sg25653,True.intro,True.intro⟩,⟨sg25655,True.intro,True.intro⟩⟩,⟨sg25658,⟨sg25657,True.intro,True.intro⟩,⟨sg25659,True.intro,True.intro⟩⟩⟩⟩,⟨sg25668,⟨sg25664,⟨sg25662,⟨sg25661,True.intro,True.intro⟩,⟨sg25663,True.intro,True.intro⟩⟩,⟨sg25666,⟨sg25665,True.intro,True.intro⟩,⟨sg25667,True.intro,True.intro⟩⟩⟩,⟨sg25672,⟨sg25670,⟨sg25669,True.intro,True.intro⟩,⟨sg25671,True.intro,True.intro⟩⟩,⟨sg25674,⟨sg25673,True.intro,True.intro⟩,⟨sg25675,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_154All_oai : degreeTree43_154.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25644,degreeTree43_152All,degreeTree43_153All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_154All_oai := @OAI.UniversalTensorSquare.degreeTree43_154All_oai
