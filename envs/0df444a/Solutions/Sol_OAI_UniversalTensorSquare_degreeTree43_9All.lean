-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_9All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:30:39.542598+00:00
-- url     : https://prove2.me/submissions/4cde83d8-a7b6-4beb-a660-818cc494dd1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_5All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10211
import Theorems.Thm_OAI_UniversalTensorSquare_sg10214
import Theorems.Thm_OAI_UniversalTensorSquare_sg10215
import Theorems.Thm_OAI_UniversalTensorSquare_sg10218
import Theorems.Thm_OAI_UniversalTensorSquare_sg10268
import Theorems.Thm_OAI_UniversalTensorSquare_sg10271
import Theorems.Thm_OAI_UniversalTensorSquare_sg11439
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg23756
import Theorems.Thm_OAI_UniversalTensorSquare_sg23758
import Theorems.Thm_OAI_UniversalTensorSquare_sg23759
import Theorems.Thm_OAI_UniversalTensorSquare_sg23760
import Theorems.Thm_OAI_UniversalTensorSquare_sg23762
import Theorems.Thm_OAI_UniversalTensorSquare_sg23764
import Theorems.Thm_OAI_UniversalTensorSquare_sg23765
import Theorems.Thm_OAI_UniversalTensorSquare_sg23766
import Theorems.Thm_OAI_UniversalTensorSquare_sg23767
import Theorems.Thm_OAI_UniversalTensorSquare_sg23768
import Theorems.Thm_OAI_UniversalTensorSquare_sg23769
import Theorems.Thm_OAI_UniversalTensorSquare_sg23770
import Theorems.Thm_OAI_UniversalTensorSquare_sg23771
import Theorems.Thm_OAI_UniversalTensorSquare_sg23772
import Theorems.Thm_OAI_UniversalTensorSquare_sg23773
import Theorems.Thm_OAI_UniversalTensorSquare_sg23774
import Theorems.Thm_OAI_UniversalTensorSquare_sg23775
import Theorems.Thm_OAI_UniversalTensorSquare_sg23777
import Theorems.Thm_OAI_UniversalTensorSquare_sg23780
import Theorems.Thm_OAI_UniversalTensorSquare_sg23781
import Theorems.Thm_OAI_UniversalTensorSquare_sg23782
import Theorems.Thm_OAI_UniversalTensorSquare_sg23783
import Theorems.Thm_OAI_UniversalTensorSquare_sg23784
import Theorems.Thm_OAI_UniversalTensorSquare_sg23785
import Theorems.Thm_OAI_UniversalTensorSquare_sg23786
import Theorems.Thm_OAI_UniversalTensorSquare_sg23788
import Theorems.Thm_OAI_UniversalTensorSquare_sg23794
import Theorems.Thm_OAI_UniversalTensorSquare_sg23796
import Theorems.Thm_OAI_UniversalTensorSquare_sg23797
import Theorems.Thm_OAI_UniversalTensorSquare_sg23798
import Theorems.Thm_OAI_UniversalTensorSquare_sg23799
import Theorems.Thm_OAI_UniversalTensorSquare_sg23800
import Theorems.Thm_OAI_UniversalTensorSquare_sg23801
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
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

lemma sgCert92 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 = 1 := by
  decide +kernel

lemma sg92 : RowSquare [4,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB92 sgT92 sgFlag92
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 ≠ 0
  rw [sgCert92]
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

lemma sgCert378 : solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB378 sgT378) sgFlag378 = 4 := by
  decide +kernel

lemma sg378 : RowSquare [5,1,1,1] [3,3,2] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [3,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB378 sgT378 sgFlag378
  change solveCompact 8 (.full [3,3,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [3,3,2] (Equiv.refl (Fin 8)) sgB378 sgT378) sgFlag378 ≠ 0
  rw [sgCert378]
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

lemma sg47 : RowSquare [4,1] [4,1] := by
  exact rowSquare_join (by decide) sg2 sg5

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg34

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg241 : RowSquare [2,2,1,1,1,1] [4,4] := by
  exact rowSquare_join (by decide) sg17 sg17

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

lemma sg265 : RowSquare [3,1,1,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg92

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg525 : RowSquare [4,1,1,1,1,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg378

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

lemma sg911 : RowSquare [5,2,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg21

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

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

lemma sg1329 : RowSquare [6,1,1,1,1,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg111

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

lemma sg1338 : RowSquare [6,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg262

lemma sg1339 : RowSquare [6,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg525

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

lemma sg1663 : RowSquare [5,2,1,1,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg586

lemma sg1875 : RowSquare [7,2,1,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg586

lemma sg1877 : RowSquare [7,2,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg588

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

lemma sg8227 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1877

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1327

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1327

lemma sg8524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1327

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

lemma sg8983 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2311

lemma sg9174 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg1875

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

lemma sg7237 : RowSquare [5,5,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg911

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

lemma sg8792 : RowSquare [7,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1663

lemma sg8873 : RowSquare [7,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg5525

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

lemma sg9699 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1338

lemma sg9700 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1373

lemma sg9703 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1339

lemma sg9704 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8227

lemma sg9705 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1373

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

lemma sg23757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10100

lemma sg23761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg8873 sg8983

lemma sg23763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg7237 sg11439

lemma sg23776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,4,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9699

lemma sg23778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,4,4,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10211

lemma sg23779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,4,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9700

lemma sg23787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9703

lemma sg23789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10268

lemma sg23790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10214

lemma sg23791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9704

lemma sg23792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10215

lemma sg23793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9705

lemma sg23795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8792 sg9174

lemma sg23802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10271

lemma sg23803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,5,5,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10218

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

lemma degreeTree43_6All : degreeTree43_6.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23764,⟨sg23760,⟨sg23758,⟨sg23757,True.intro,True.intro⟩,⟨sg23759,True.intro,True.intro⟩⟩,⟨sg23762,⟨sg23761,True.intro,True.intro⟩,⟨sg23763,True.intro,True.intro⟩⟩⟩,⟨sg23768,⟨sg23766,⟨sg23765,True.intro,True.intro⟩,⟨sg23767,True.intro,True.intro⟩⟩,⟨sg23770,⟨sg23769,True.intro,True.intro⟩,⟨sg23771,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_7All : degreeTree43_7.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23756,degreeTree43_5All,degreeTree43_6All⟩

lemma degreeTree43_8All : degreeTree43_8.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23788,⟨sg23780,⟨sg23776,⟨sg23774,⟨sg23773,True.intro,True.intro⟩,⟨sg23775,True.intro,True.intro⟩⟩,⟨sg23778,⟨sg23777,True.intro,True.intro⟩,⟨sg23779,True.intro,True.intro⟩⟩⟩,⟨sg23784,⟨sg23782,⟨sg23781,True.intro,True.intro⟩,⟨sg23783,True.intro,True.intro⟩⟩,⟨sg23786,⟨sg23785,True.intro,True.intro⟩,⟨sg23787,True.intro,True.intro⟩⟩⟩⟩,⟨sg23796,⟨sg23792,⟨sg23790,⟨sg23789,True.intro,True.intro⟩,⟨sg23791,True.intro,True.intro⟩⟩,⟨sg23794,⟨sg23793,True.intro,True.intro⟩,⟨sg23795,True.intro,True.intro⟩⟩⟩,⟨sg23800,⟨sg23798,⟨sg23797,True.intro,True.intro⟩,⟨sg23799,True.intro,True.intro⟩⟩,⟨sg23802,⟨sg23801,True.intro,True.intro⟩,⟨sg23803,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_9All_oai : degreeTree43_9.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23772,degreeTree43_7All,degreeTree43_8All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_9All_oai := @OAI.UniversalTensorSquare.degreeTree43_9All_oai
