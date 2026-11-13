-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_9All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:50:24.202204+00:00
-- url     : https://prove2.me/submissions/3355e672-6844-44ab-a175-3feafb9ae418
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21789
import Theorems.Thm_OAI_UniversalTensorSquare_sg21790
import Theorems.Thm_OAI_UniversalTensorSquare_sg21791
import Theorems.Thm_OAI_UniversalTensorSquare_sg21792
import Theorems.Thm_OAI_UniversalTensorSquare_sg21793
import Theorems.Thm_OAI_UniversalTensorSquare_sg21794
import Theorems.Thm_OAI_UniversalTensorSquare_sg21795
import Theorems.Thm_OAI_UniversalTensorSquare_sg21796
import Theorems.Thm_OAI_UniversalTensorSquare_sg21797
import Theorems.Thm_OAI_UniversalTensorSquare_sg21798
import Theorems.Thm_OAI_UniversalTensorSquare_sg21799
import Theorems.Thm_OAI_UniversalTensorSquare_sg21801
import Theorems.Thm_OAI_UniversalTensorSquare_sg21802
import Theorems.Thm_OAI_UniversalTensorSquare_sg21803
import Theorems.Thm_OAI_UniversalTensorSquare_sg21805
import Theorems.Thm_OAI_UniversalTensorSquare_sg21806
import Theorems.Thm_OAI_UniversalTensorSquare_sg21808
import Theorems.Thm_OAI_UniversalTensorSquare_sg21810
import Theorems.Thm_OAI_UniversalTensorSquare_sg21812
import Theorems.Thm_OAI_UniversalTensorSquare_sg21813
import Theorems.Thm_OAI_UniversalTensorSquare_sg21814
import Theorems.Thm_OAI_UniversalTensorSquare_sg21815
import Theorems.Thm_OAI_UniversalTensorSquare_sg21817
import Theorems.Thm_OAI_UniversalTensorSquare_sg21818
import Theorems.Thm_OAI_UniversalTensorSquare_sg21819
import Theorems.Thm_OAI_UniversalTensorSquare_sg21820
import Theorems.Thm_OAI_UniversalTensorSquare_sg21821
import Theorems.Thm_OAI_UniversalTensorSquare_sg21822
import Theorems.Thm_OAI_UniversalTensorSquare_sg21823
import Theorems.Thm_OAI_UniversalTensorSquare_sg21824
import Theorems.Thm_OAI_UniversalTensorSquare_sg21826
import Theorems.Thm_OAI_UniversalTensorSquare_sg21829
import Theorems.Thm_OAI_UniversalTensorSquare_sg21830
import Theorems.Thm_OAI_UniversalTensorSquare_sg21833
import Theorems.Thm_OAI_UniversalTensorSquare_sg21834
import Theorems.Thm_OAI_UniversalTensorSquare_sg21835
import Theorems.Thm_OAI_UniversalTensorSquare_sg21837
import Theorems.Thm_OAI_UniversalTensorSquare_sg21838
import Theorems.Thm_OAI_UniversalTensorSquare_sg21839
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6305
import Theorems.Thm_OAI_UniversalTensorSquare_sg6418
import Theorems.Thm_OAI_UniversalTensorSquare_sg6640
import Theorems.Thm_OAI_UniversalTensorSquare_sg6641
import Theorems.Thm_OAI_UniversalTensorSquare_sg6642
import Theorems.Thm_OAI_UniversalTensorSquare_sg6779
import Theorems.Thm_OAI_UniversalTensorSquare_sg6788
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7563
import Theorems.Thm_OAI_UniversalTensorSquare_sg7583
import Theorems.Thm_OAI_UniversalTensorSquare_sg7585
import Theorems.Thm_OAI_UniversalTensorSquare_sg7587
import Theorems.Thm_OAI_UniversalTensorSquare_sg7588
import Theorems.Thm_OAI_UniversalTensorSquare_sg7589
import Theorems.Thm_OAI_UniversalTensorSquare_sg7590
import Theorems.Thm_OAI_UniversalTensorSquare_sg7591
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

lemma sgCert324 : solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB324 sgT324) sgFlag324 = 4 := by
  decide +kernel

lemma sg324 : RowSquare [4,1,1,1,1] [4,4] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB324 sgT324 sgFlag324
  change solveCompact 8 (.full [2,2,2,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [2,2,2,2] (Equiv.refl (Fin 8)) sgB324 sgT324) sgFlag324 ≠ 0
  rw [sgCert324]
  norm_num

end UniversalTensorSquare
end
end

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

lemma sg80 : RowSquare [3,2,1] [3,3] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [3,3])
  have hh : SquareOccurs (staircase 3) (rowDiagram [3,3]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [3,3]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [3,3])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,3])) he) hh

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg273 : RowSquare [3,2,1,1,1] [3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg32

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

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

lemma sg1686 : RowSquare [5,3,2,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg53

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

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

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

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

lemma sg6782 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1416

lemma sg6785 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1417

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

lemma sg6151 : RowSquare [5,4,3,2,1,1,1,1,1] [3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg850

lemma sg6154 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1686

lemma sg6416 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg273 sg1327

lemma sg6417 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5601

lemma sg6473 : RowSquare [7,5,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3964

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

lemma sg7314 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1757

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21788 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7583

lemma sg21800 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7585

lemma sg21804 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6779

lemma sg21807 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7587

lemma sg21809 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7588

lemma sg21811 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6782

lemma sg21816 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7589

lemma sg21825 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7590

lemma sg21827 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6305 sg7314

lemma sg21828 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7591

lemma sg21831 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6418 sg6785

lemma sg21832 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6640

lemma sg21836 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6641

lemma sg21840 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg6154 sg7563

lemma sg21841 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6788

lemma sg21842 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6788

lemma sg21843 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6642

lemma sg21844 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg6418 sg6788

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

lemma degreeTree39_7All : degreeTree39_7.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21802,⟨sg21795,⟨sg21791,⟨sg21789,⟨sg21788,True.intro,True.intro⟩,⟨sg21790,True.intro,True.intro⟩⟩,⟨sg21793,⟨sg21792,True.intro,True.intro⟩,⟨sg21794,True.intro,True.intro⟩⟩⟩,⟨sg21799,⟨sg21797,⟨sg21796,True.intro,True.intro⟩,⟨sg21798,True.intro,True.intro⟩⟩,⟨sg21801,⟨sg21800,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21809,⟨sg21806,⟨sg21804,⟨sg21803,True.intro,True.intro⟩,⟨sg21805,True.intro,True.intro⟩⟩,⟨sg21808,⟨sg21807,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21813,⟨sg21811,⟨sg21810,True.intro,True.intro⟩,⟨sg21812,True.intro,True.intro⟩⟩,⟨sg21815,⟨sg21814,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_8All : degreeTree39_8.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21831,⟨sg21824,⟨sg21820,⟨sg21818,⟨sg21817,True.intro,True.intro⟩,⟨sg21819,True.intro,True.intro⟩⟩,⟨sg21822,⟨sg21821,True.intro,True.intro⟩,⟨sg21823,True.intro,True.intro⟩⟩⟩,⟨sg21828,⟨sg21826,⟨sg21825,True.intro,True.intro⟩,⟨sg21827,True.intro,True.intro⟩⟩,⟨sg21830,⟨sg21829,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21838,⟨sg21835,⟨sg21833,⟨sg21832,True.intro,True.intro⟩,⟨sg21834,True.intro,True.intro⟩⟩,⟨sg21837,⟨sg21836,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21842,⟨sg21840,⟨sg21839,True.intro,True.intro⟩,⟨sg21841,True.intro,True.intro⟩⟩,⟨sg21844,⟨sg21843,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_9All_oai : degreeTree39_9.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21816,degreeTree39_7All,degreeTree39_8All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_9All_oai := @OAI.UniversalTensorSquare.degreeTree39_9All_oai
