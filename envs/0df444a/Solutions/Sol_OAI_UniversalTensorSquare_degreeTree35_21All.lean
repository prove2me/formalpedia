-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree35_21All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:15:35.170415+00:00
-- url     : https://prove2.me/submissions/0994ede4-f029-4e71-a30a-7da2de78fc8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg21579
import Theorems.Thm_OAI_UniversalTensorSquare_sg21580
import Theorems.Thm_OAI_UniversalTensorSquare_sg21581
import Theorems.Thm_OAI_UniversalTensorSquare_sg21582
import Theorems.Thm_OAI_UniversalTensorSquare_sg21583
import Theorems.Thm_OAI_UniversalTensorSquare_sg21585
import Theorems.Thm_OAI_UniversalTensorSquare_sg21586
import Theorems.Thm_OAI_UniversalTensorSquare_sg21587
import Theorems.Thm_OAI_UniversalTensorSquare_sg21588
import Theorems.Thm_OAI_UniversalTensorSquare_sg21589
import Theorems.Thm_OAI_UniversalTensorSquare_sg21591
import Theorems.Thm_OAI_UniversalTensorSquare_sg21592
import Theorems.Thm_OAI_UniversalTensorSquare_sg21593
import Theorems.Thm_OAI_UniversalTensorSquare_sg21595
import Theorems.Thm_OAI_UniversalTensorSquare_sg21596
import Theorems.Thm_OAI_UniversalTensorSquare_sg21597
import Theorems.Thm_OAI_UniversalTensorSquare_sg21598
import Theorems.Thm_OAI_UniversalTensorSquare_sg21600
import Theorems.Thm_OAI_UniversalTensorSquare_sg21602
import Theorems.Thm_OAI_UniversalTensorSquare_sg21603
import Theorems.Thm_OAI_UniversalTensorSquare_sg21605
import Theorems.Thm_OAI_UniversalTensorSquare_sg21607
import Theorems.Thm_OAI_UniversalTensorSquare_sg21608
import Theorems.Thm_OAI_UniversalTensorSquare_sg5276
import Theorems.Thm_OAI_UniversalTensorSquare_sg5488
import Theorems.Thm_OAI_UniversalTensorSquare_sg5490
import Theorems.Thm_OAI_UniversalTensorSquare_sg5495
import Theorems.Thm_OAI_UniversalTensorSquare_sg5500
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

lemma sgCert68 : solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB68 sgT68) sgFlag68 = 6 := by
  decide +kernel

lemma sg68 : RowSquare [3,1,1,1] [2,2,2] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB68 sgT68 sgFlag68
  change solveCompact 6 (.full [3,3]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [3,3] (Equiv.refl (Fin 6)) sgB68 sgT68) sgFlag68 ≠ 0
  rw [sgCert68]
  norm_num

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert143 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 = 6 := by
  decide +kernel

lemma sg143 : RowSquare [3,2,1,1] [2,2,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [5,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB143 sgT143 sgFlag143
  change solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 ≠ 0
  rw [sgCert143]
  norm_num

lemma sgCert144 : solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 = 2 := by
  decide +kernel

lemma sg144 : RowSquare [3,2,1,1] [2,2,2,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,1,1]) (ts := [4,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB144 sgT144 sgFlag144
  change solveCompact 7 (.full [4,3]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [4,3] (Equiv.refl (Fin 7)) sgB144 sgT144) sgFlag144 ≠ 0
  rw [sgCert144]
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

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

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

lemma sg3984 : RowSquare [5,4,2,1,1,1,1,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg910

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

lemma sg4784 : RowSquare [5,4,2,2,1,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg910

lemma sg4785 : RowSquare [5,4,2,2,1,1,1,1] [3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg143 sg910

lemma sg4786 : RowSquare [5,4,2,2,1,1,1,1] [3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg910

lemma sg4854 : RowSquare [6,4,2,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3984

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21578 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5488

lemma sg21584 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5490

lemma sg21590 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5500

lemma sg21594 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5495

lemma sg21599 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5495

lemma sg21601 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4854 sg5276

lemma sg21604 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5500

lemma sg21606 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5500

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree35_21All_oai : degreeTree35_21.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21593,⟨sg21585,⟨sg21581,⟨sg21579,⟨sg21578,True.intro,True.intro⟩,⟨sg21580,True.intro,True.intro⟩⟩,⟨sg21583,⟨sg21582,True.intro,True.intro⟩,⟨sg21584,True.intro,True.intro⟩⟩⟩,⟨sg21589,⟨sg21587,⟨sg21586,True.intro,True.intro⟩,⟨sg21588,True.intro,True.intro⟩⟩,⟨sg21591,⟨sg21590,True.intro,True.intro⟩,⟨sg21592,True.intro,True.intro⟩⟩⟩⟩,⟨sg21601,⟨sg21597,⟨sg21595,⟨sg21594,True.intro,True.intro⟩,⟨sg21596,True.intro,True.intro⟩⟩,⟨sg21599,⟨sg21598,True.intro,True.intro⟩,⟨sg21600,True.intro,True.intro⟩⟩⟩,⟨sg21605,⟨sg21603,⟨sg21602,True.intro,True.intro⟩,⟨sg21604,True.intro,True.intro⟩⟩,⟨sg21607,⟨sg21606,True.intro,True.intro⟩,⟨sg21608,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree35_21All_oai := @OAI.UniversalTensorSquare.degreeTree35_21All_oai
