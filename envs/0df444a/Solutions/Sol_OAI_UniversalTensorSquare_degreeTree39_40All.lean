-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_40All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:29:46.814793+00:00
-- url     : https://prove2.me/submissions/7f6b5a73-4afe-4b41-871d-7a1d0379a12a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_39All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg22253
import Theorems.Thm_OAI_UniversalTensorSquare_sg22255
import Theorems.Thm_OAI_UniversalTensorSquare_sg22256
import Theorems.Thm_OAI_UniversalTensorSquare_sg22258
import Theorems.Thm_OAI_UniversalTensorSquare_sg22259
import Theorems.Thm_OAI_UniversalTensorSquare_sg22261
import Theorems.Thm_OAI_UniversalTensorSquare_sg22263
import Theorems.Thm_OAI_UniversalTensorSquare_sg22264
import Theorems.Thm_OAI_UniversalTensorSquare_sg22266
import Theorems.Thm_OAI_UniversalTensorSquare_sg22267
import Theorems.Thm_OAI_UniversalTensorSquare_sg22268
import Theorems.Thm_OAI_UniversalTensorSquare_sg22270
import Theorems.Thm_OAI_UniversalTensorSquare_sg22271
import Theorems.Thm_OAI_UniversalTensorSquare_sg22272
import Theorems.Thm_OAI_UniversalTensorSquare_sg22273
import Theorems.Thm_OAI_UniversalTensorSquare_sg22274
import Theorems.Thm_OAI_UniversalTensorSquare_sg22276
import Theorems.Thm_OAI_UniversalTensorSquare_sg22277
import Theorems.Thm_OAI_UniversalTensorSquare_sg22278
import Theorems.Thm_OAI_UniversalTensorSquare_sg22279
import Theorems.Thm_OAI_UniversalTensorSquare_sg22280
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7653
import Theorems.Thm_OAI_UniversalTensorSquare_sg7654
import Theorems.Thm_OAI_UniversalTensorSquare_sg7655
import Theorems.Thm_OAI_UniversalTensorSquare_sg7656
import Theorems.Thm_OAI_UniversalTensorSquare_sg7657
import Theorems.Thm_OAI_UniversalTensorSquare_sg7658
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

lemma sgCert314 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 = 20 := by
  decide +kernel

lemma sg314 : RowSquare [4,1,1,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB314 sgT314 sgFlag314
  change solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 ≠ 0
  rw [sgCert314]
  norm_num

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

lemma sg1049 : RowSquare [6,2,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg68

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

lemma sg5602 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg910

lemma sg5604 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg910

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

lemma sg6808 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1049

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

lemma sg6421 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5602

lemma sg6424 : RowSquare [6,5,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5604

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22254 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7653

lemma sg22257 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6808

lemma sg22260 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7654

lemma sg22262 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6808

lemma sg22265 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7655

lemma sg22269 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7656

lemma sg22275 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7657

lemma sg22281 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7658

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

lemma degreeTree39_38All : degreeTree39_38.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22267,⟨sg22260,⟨sg22256,⟨sg22254,⟨sg22253,True.intro,True.intro⟩,⟨sg22255,True.intro,True.intro⟩⟩,⟨sg22258,⟨sg22257,True.intro,True.intro⟩,⟨sg22259,True.intro,True.intro⟩⟩⟩,⟨sg22264,⟨sg22262,⟨sg22261,True.intro,True.intro⟩,⟨sg22263,True.intro,True.intro⟩⟩,⟨sg22266,⟨sg22265,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22274,⟨sg22271,⟨sg22269,⟨sg22268,True.intro,True.intro⟩,⟨sg22270,True.intro,True.intro⟩⟩,⟨sg22273,⟨sg22272,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22278,⟨sg22276,⟨sg22275,True.intro,True.intro⟩,⟨sg22277,True.intro,True.intro⟩⟩,⟨sg22280,⟨sg22279,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_40All_oai : degreeTree39_40.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22281,degreeTree39_38All,degreeTree39_39All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_40All_oai := @OAI.UniversalTensorSquare.degreeTree39_40All_oai
