-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree35_16All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:15:25.210754+00:00
-- url     : https://prove2.me/submissions/7df97fb1-941d-4f15-adc9-2d6a3ba41c98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg122
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg15
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg21513
import Theorems.Thm_OAI_UniversalTensorSquare_sg21514
import Theorems.Thm_OAI_UniversalTensorSquare_sg21515
import Theorems.Thm_OAI_UniversalTensorSquare_sg21516
import Theorems.Thm_OAI_UniversalTensorSquare_sg21521
import Theorems.Thm_OAI_UniversalTensorSquare_sg21522
import Theorems.Thm_OAI_UniversalTensorSquare_sg21523
import Theorems.Thm_OAI_UniversalTensorSquare_sg21525
import Theorems.Thm_OAI_UniversalTensorSquare_sg21526
import Theorems.Thm_OAI_UniversalTensorSquare_sg21527
import Theorems.Thm_OAI_UniversalTensorSquare_sg21529
import Theorems.Thm_OAI_UniversalTensorSquare_sg21530
import Theorems.Thm_OAI_UniversalTensorSquare_sg21531
import Theorems.Thm_OAI_UniversalTensorSquare_sg21532
import Theorems.Thm_OAI_UniversalTensorSquare_sg21533
import Theorems.Thm_OAI_UniversalTensorSquare_sg21534
import Theorems.Thm_OAI_UniversalTensorSquare_sg21535
import Theorems.Thm_OAI_UniversalTensorSquare_sg21536
import Theorems.Thm_OAI_UniversalTensorSquare_sg21537
import Theorems.Thm_OAI_UniversalTensorSquare_sg21538
import Theorems.Thm_OAI_UniversalTensorSquare_sg21541
import Theorems.Thm_OAI_UniversalTensorSquare_sg21542
import Theorems.Thm_OAI_UniversalTensorSquare_sg21543
import Theorems.Thm_OAI_UniversalTensorSquare_sg2596
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg4734
import Theorems.Thm_OAI_UniversalTensorSquare_sg54
import Theorems.Thm_OAI_UniversalTensorSquare_sg5439
import Theorems.Thm_OAI_UniversalTensorSquare_sg5488
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8
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

lemma sgCert71 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 = 2 := by
  decide +kernel

lemma sg71 : RowSquare [3,1,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB71 sgT71 sgFlag71
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 ≠ 0
  rw [sgCert71]
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

lemma sg82 : RowSquare [3,2,1] [5,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [5,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [5,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [5,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [5,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [5,1])) he) hh

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg153 : RowSquare [3,2,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg8

lemma sg233 : RowSquare [6,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg379 : RowSquare [5,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg66

lemma sg386 : RowSquare [5,1,1,1] [5,3] := by
  exact rowSquare_join (by decide) sg2 sg71

lemma sg413 : RowSquare [6,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg603 : RowSquare [5,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg132

lemma sg651 : RowSquare [5,3,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg32

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

lemma sg1683 : RowSquare [5,3,2,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg82 sg54

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

lemma sg2512 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg233

lemma sg2597 : RowSquare [5,4,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg153 sg122

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

lemma sg3186 : RowSquare [4,3,1,1,1,1,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg413

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

lemma sg3896 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg379

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

lemma sg4718 : RowSquare [4,4,3,2,1,1,1,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg849

lemma sg4737 : RowSquare [5,3,3,2,1,1,1,1] [3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1683

lemma sg4784 : RowSquare [5,4,2,2,1,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg910

lemma sg4787 : RowSquare [5,4,2,2,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2596

lemma sg4790 : RowSquare [5,4,2,2,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg2597

lemma sg4822 : RowSquare [5,5,2,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg910

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

lemma sg5358 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg651

lemma sg5466 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg386 sg910

lemma sg5589 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg603

lemma sg5597 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3896

lemma sg5637 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3186

lemma sg5641 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2512

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

lemma sg21517 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5439

lemma sg21518 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5597

lemma sg21519 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4737 sg5589

lemma sg21520 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4822 sg5358

lemma sg21524 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5637

lemma sg21528 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5466

lemma sg21539 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5488

lemma sg21540 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5641

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

lemma degreeTree35_16All_oai : degreeTree35_16.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21528,⟨sg21520,⟨sg21516,⟨sg21514,⟨sg21513,True.intro,True.intro⟩,⟨sg21515,True.intro,True.intro⟩⟩,⟨sg21518,⟨sg21517,True.intro,True.intro⟩,⟨sg21519,True.intro,True.intro⟩⟩⟩,⟨sg21524,⟨sg21522,⟨sg21521,True.intro,True.intro⟩,⟨sg21523,True.intro,True.intro⟩⟩,⟨sg21526,⟨sg21525,True.intro,True.intro⟩,⟨sg21527,True.intro,True.intro⟩⟩⟩⟩,⟨sg21536,⟨sg21532,⟨sg21530,⟨sg21529,True.intro,True.intro⟩,⟨sg21531,True.intro,True.intro⟩⟩,⟨sg21534,⟨sg21533,True.intro,True.intro⟩,⟨sg21535,True.intro,True.intro⟩⟩⟩,⟨sg21540,⟨sg21538,⟨sg21537,True.intro,True.intro⟩,⟨sg21539,True.intro,True.intro⟩⟩,⟨sg21542,⟨sg21541,True.intro,True.intro⟩,⟨sg21543,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree35_16All_oai := @OAI.UniversalTensorSquare.degreeTree35_16All_oai
