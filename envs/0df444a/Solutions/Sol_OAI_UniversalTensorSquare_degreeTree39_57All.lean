-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_57All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:30:11.436005+00:00
-- url     : https://prove2.me/submissions/3521000f-7bae-4f8f-8331-a8cfdd89ee02
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg113
import Theorems.Thm_OAI_UniversalTensorSquare_sg12
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg22572
import Theorems.Thm_OAI_UniversalTensorSquare_sg22573
import Theorems.Thm_OAI_UniversalTensorSquare_sg22578
import Theorems.Thm_OAI_UniversalTensorSquare_sg22579
import Theorems.Thm_OAI_UniversalTensorSquare_sg22584
import Theorems.Thm_OAI_UniversalTensorSquare_sg22585
import Theorems.Thm_OAI_UniversalTensorSquare_sg22586
import Theorems.Thm_OAI_UniversalTensorSquare_sg22587
import Theorems.Thm_OAI_UniversalTensorSquare_sg22588
import Theorems.Thm_OAI_UniversalTensorSquare_sg22589
import Theorems.Thm_OAI_UniversalTensorSquare_sg22590
import Theorems.Thm_OAI_UniversalTensorSquare_sg22591
import Theorems.Thm_OAI_UniversalTensorSquare_sg22592
import Theorems.Thm_OAI_UniversalTensorSquare_sg22596
import Theorems.Thm_OAI_UniversalTensorSquare_sg22599
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg5298
import Theorems.Thm_OAI_UniversalTensorSquare_sg54
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6147
import Theorems.Thm_OAI_UniversalTensorSquare_sg6157
import Theorems.Thm_OAI_UniversalTensorSquare_sg6245
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7483
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

lemma sg47 : RowSquare [4,1] [4,1] := by
  exact rowSquare_join (by decide) sg2 sg5

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg66 : RowSquare [3,1,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg205 : RowSquare [4,2,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg12

lemma sg218 : RowSquare [5,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg260 : RowSquare [3,1,1,1,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg303 : RowSquare [3,3,1,1] [5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg8

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg530 : RowSquare [4,1,1,1,1,1] [5,4] := by
  exact rowSquare_join (by decide) sg0 sg383

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg603 : RowSquare [5,1,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg132

lemma sg608 : RowSquare [5,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg135

lemma sg673 : RowSquare [6,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg682 : RowSquare [6,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg66

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1002 : RowSquare [6,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg587

lemma sg1024 : RowSquare [6,1,1,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg132

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

lemma sg2021 : RowSquare [3,3,1,1,1,1,1,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg218

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

lemma sg2627 : RowSquare [6,3,2,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg205 sg113

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

lemma sg4643 : RowSquare [4,4,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg673

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

lemma sg5399 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg682

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

lemma sg6148 : RowSquare [5,4,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg849

lemma sg6150 : RowSquare [5,4,3,2,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1683

lemma sg6170 : RowSquare [5,4,3,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5298

lemma sg6203 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1002

lemma sg6283 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg4643

lemma sg6364 : RowSquare [6,4,2,2,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg1754

lemma sg6381 : RowSquare [6,4,2,2,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg303 sg1327

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

lemma sg7480 : RowSquare [6,4,3,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg2626

lemma sg7490 : RowSquare [6,4,3,2,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg2627

lemma sg7517 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1331

lemma sg7592 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg603 sg1327

lemma sg7659 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg1327

lemma sg7660 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg603 sg1328

lemma sg7721 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg1328

lemma sg7722 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5399

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

lemma sg7029 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg911

lemma sg7174 : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1024

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12941 : RowSquare [8,6,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg260 sg5735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 55. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22574 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6170 sg7517

lemma sg22575 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7721

lemma sg22576 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6150 sg7659

lemma sg22577 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6203 sg7490

lemma sg22580 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6381 sg7029

lemma sg22581 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6148 sg7721

lemma sg22582 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2021 sg12941

lemma sg22583 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6245 sg7483

lemma sg22593 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7174

lemma sg22594 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6157 sg7592

lemma sg22595 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6283 sg7480

lemma sg22597 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7722

lemma sg22598 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,4,4,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6150 sg7660

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

lemma degreeTree39_57All_oai : degreeTree39_57.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22586,⟨sg22579,⟨sg22575,⟨sg22573,⟨sg22572,True.intro,True.intro⟩,⟨sg22574,True.intro,True.intro⟩⟩,⟨sg22577,⟨sg22576,True.intro,True.intro⟩,⟨sg22578,True.intro,True.intro⟩⟩⟩,⟨sg22583,⟨sg22581,⟨sg22580,True.intro,True.intro⟩,⟨sg22582,True.intro,True.intro⟩⟩,⟨sg22585,⟨sg22584,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22593,⟨sg22590,⟨sg22588,⟨sg22587,True.intro,True.intro⟩,⟨sg22589,True.intro,True.intro⟩⟩,⟨sg22592,⟨sg22591,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22597,⟨sg22595,⟨sg22594,True.intro,True.intro⟩,⟨sg22596,True.intro,True.intro⟩⟩,⟨sg22599,⟨sg22598,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_57All_oai := @OAI.UniversalTensorSquare.degreeTree39_57All_oai
