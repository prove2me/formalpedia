-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_133All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:51:00.784735+00:00
-- url     : https://prove2.me/submissions/d1d06d45-c474-41cb-ac38-5ba32bffaae2
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
import Theorems.Thm_OAI_UniversalTensorSquare_sg1232
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg25354
import Theorems.Thm_OAI_UniversalTensorSquare_sg25357
import Theorems.Thm_OAI_UniversalTensorSquare_sg25358
import Theorems.Thm_OAI_UniversalTensorSquare_sg25359
import Theorems.Thm_OAI_UniversalTensorSquare_sg25361
import Theorems.Thm_OAI_UniversalTensorSquare_sg25363
import Theorems.Thm_OAI_UniversalTensorSquare_sg25366
import Theorems.Thm_OAI_UniversalTensorSquare_sg25371
import Theorems.Thm_OAI_UniversalTensorSquare_sg25372
import Theorems.Thm_OAI_UniversalTensorSquare_sg25373
import Theorems.Thm_OAI_UniversalTensorSquare_sg25374
import Theorems.Thm_OAI_UniversalTensorSquare_sg25375
import Theorems.Thm_OAI_UniversalTensorSquare_sg25378
import Theorems.Thm_OAI_UniversalTensorSquare_sg25379
import Theorems.Thm_OAI_UniversalTensorSquare_sg25381
import Theorems.Thm_OAI_UniversalTensorSquare_sg25383
import Theorems.Thm_OAI_UniversalTensorSquare_sg25384
import Theorems.Thm_OAI_UniversalTensorSquare_sg25385
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg54
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg8559
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9530

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

lemma sgCert809 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 = -40 := by
  decide +kernel

lemma sg809 : RowSquare [4,2,1,1,1,1] [2,2,2,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [5,5])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB809 sgT809 sgFlag809
  change solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 ≠ 0
  rw [sgCert809]
  norm_num

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

lemma sgCert271 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 = -4 := by
  decide +kernel

lemma sg271 : RowSquare [3,2,1,1,1] [2,2,2,2] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB271 sgT271 sgFlag271
  change solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 ≠ 0
  rw [sgCert271]
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

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg218 : RowSquare [5,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg231 : RowSquare [6,1] [5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg20

lemma sg517 : RowSquare [4,1,1,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

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

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1002 : RowSquare [6,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg587

lemma sg1003 : RowSquare [6,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg588

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

lemma sg1350 : RowSquare [6,1,1,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg517

lemma sg1372 : RowSquare [6,2,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg586

lemma sg1373 : RowSquare [6,2,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg912

lemma sg1503 : RowSquare [7,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg587

lemma sg1504 : RowSquare [7,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg588

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

lemma sg1675 : RowSquare [5,2,2,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

lemma sg1683 : RowSquare [5,3,2,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg82 sg54

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

lemma sg2136 : RowSquare [5,3,2,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg271

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

lemma sg5131 : RowSquare [4,3,3,2,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg1232

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6024 : RowSquare [5,3,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg218 sg1683

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

lemma sg6905 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg997

lemma sg6920 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1002

lemma sg6921 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1003

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

lemma sg8230 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1503

lemma sg8231 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg1372

lemma sg8232 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1504

lemma sg8233 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1373

lemma sg8415 : RowSquare [6,4,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg1327

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg850 sg1327

lemma sg8511 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6024

lemma sg8514 : RowSquare [6,4,3,2,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5131

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10167 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1327

lemma sg10245 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1350

lemma sg10247 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6905

lemma sg10322 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1350

lemma sg10323 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6920

lemma sg10326 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6921

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

lemma sg9763 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8230

lemma sg9764 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8231

lemma sg9767 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8232

lemma sg9768 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8233

lemma sg10095 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1675

lemma sg10096 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2136

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

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

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

lemma sg25355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9530

lemma sg25356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10095

lemma sg25360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10096

lemma sg25362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8511 sg10167

lemma sg25364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10245

lemma sg25365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10322

lemma sg25367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10323

lemma sg25368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9763

lemma sg25369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10247

lemma sg25370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8648 sg9764

lemma sg25376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10326

lemma sg25377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9767

lemma sg25380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9768

lemma sg25382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8514 sg10167

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

lemma degreeTree43_131All : degreeTree43_131.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25362,⟨sg25358,⟨sg25356,⟨sg25355,⟨sg25354,True.intro,True.intro⟩,True.intro⟩,⟨sg25357,True.intro,True.intro⟩⟩,⟨sg25360,⟨sg25359,True.intro,True.intro⟩,⟨sg25361,True.intro,True.intro⟩⟩⟩,⟨sg25366,⟨sg25364,⟨sg25363,True.intro,True.intro⟩,⟨sg25365,True.intro,True.intro⟩⟩,⟨sg25368,⟨sg25367,True.intro,True.intro⟩,⟨sg25369,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_132All : degreeTree43_132.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25378,⟨sg25374,⟨sg25372,⟨sg25371,True.intro,True.intro⟩,⟨sg25373,True.intro,True.intro⟩⟩,⟨sg25376,⟨sg25375,True.intro,True.intro⟩,⟨sg25377,True.intro,True.intro⟩⟩⟩,⟨sg25382,⟨sg25380,⟨sg25379,True.intro,True.intro⟩,⟨sg25381,True.intro,True.intro⟩⟩,⟨sg25384,⟨sg25383,True.intro,True.intro⟩,⟨sg25385,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_133All_oai : degreeTree43_133.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25370,degreeTree43_131All,degreeTree43_132All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_133All_oai := @OAI.UniversalTensorSquare.degreeTree43_133All_oai
