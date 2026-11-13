-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree35_23All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:15:37.562755+00:00
-- url     : https://prove2.me/submissions/03c70916-c1ba-474e-92d3-be8a8ddbc511
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_14All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_16All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_22All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg21480
import Theorems.Thm_OAI_UniversalTensorSquare_sg21481
import Theorems.Thm_OAI_UniversalTensorSquare_sg21482
import Theorems.Thm_OAI_UniversalTensorSquare_sg21483
import Theorems.Thm_OAI_UniversalTensorSquare_sg21484
import Theorems.Thm_OAI_UniversalTensorSquare_sg21485
import Theorems.Thm_OAI_UniversalTensorSquare_sg21490
import Theorems.Thm_OAI_UniversalTensorSquare_sg21491
import Theorems.Thm_OAI_UniversalTensorSquare_sg21492
import Theorems.Thm_OAI_UniversalTensorSquare_sg21493
import Theorems.Thm_OAI_UniversalTensorSquare_sg21495
import Theorems.Thm_OAI_UniversalTensorSquare_sg21512
import Theorems.Thm_OAI_UniversalTensorSquare_sg21544
import Theorems.Thm_OAI_UniversalTensorSquare_sg2596
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg4734
import Theorems.Thm_OAI_UniversalTensorSquare_sg4735
import Theorems.Thm_OAI_UniversalTensorSquare_sg5129
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
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

lemma sg22 : RowSquare [2,1,1,1] [3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4

lemma sg51 : RowSquare [2,1,1,1,1] [4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg387 : RowSquare [5,1,1,1] [6,1,1] := by
  exact rowSquare_join (by decide) sg7 sg22

lemma sg389 : RowSquare [5,2,1] [2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg32

lemma sg413 : RowSquare [6,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg603 : RowSquare [5,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg132

lemma sg611 : RowSquare [5,1,1,1,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg7 sg51

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

lemma sg3832 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg389

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

lemma sg4787 : RowSquare [5,4,2,2,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2596

lemma sg4873 : RowSquare [6,5,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg51 sg1327

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

lemma sg5461 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3832

lemma sg5483 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg387 sg910

lemma sg5589 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg603

lemma sg5595 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg611

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

lemma sg5128 : RowSquare [4,3,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg413 sg849

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

lemma sg21486 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5461

lemma sg21487 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4735 sg5589

lemma sg21488 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5595

lemma sg21489 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4873 sg5128

lemma sg21494 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4784 sg5483

lemma sg21496 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4873 sg5129

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

lemma degreeTree35_13All : degreeTree35_13.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21488,⟨sg21484,⟨sg21482,⟨sg21481,⟨sg21480,True.intro,True.intro⟩,True.intro⟩,⟨sg21483,True.intro,True.intro⟩⟩,⟨sg21486,⟨sg21485,True.intro,True.intro⟩,⟨sg21487,True.intro,True.intro⟩⟩⟩,⟨sg21492,⟨sg21490,⟨sg21489,True.intro,True.intro⟩,⟨sg21491,True.intro,True.intro⟩⟩,⟨sg21494,⟨sg21493,True.intro,True.intro⟩,⟨sg21495,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_15All : degreeTree35_15.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21496,degreeTree35_13All,degreeTree35_14All⟩

lemma degreeTree35_17All : degreeTree35_17.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21512,degreeTree35_15All,degreeTree35_16All⟩

lemma degreeTree35_23All_oai : degreeTree35_23.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21544,degreeTree35_17All,degreeTree35_22All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree35_23All_oai := @OAI.UniversalTensorSquare.degreeTree35_23All_oai
