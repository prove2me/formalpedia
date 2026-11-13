-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_125All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:50:58.156441+00:00
-- url     : https://prove2.me/submissions/a3dbf374-2f63-48df-8e7a-d9f97c8c73ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg25258
import Theorems.Thm_OAI_UniversalTensorSquare_sg25260
import Theorems.Thm_OAI_UniversalTensorSquare_sg25261
import Theorems.Thm_OAI_UniversalTensorSquare_sg25262
import Theorems.Thm_OAI_UniversalTensorSquare_sg25264
import Theorems.Thm_OAI_UniversalTensorSquare_sg25265
import Theorems.Thm_OAI_UniversalTensorSquare_sg25266
import Theorems.Thm_OAI_UniversalTensorSquare_sg25267
import Theorems.Thm_OAI_UniversalTensorSquare_sg25268
import Theorems.Thm_OAI_UniversalTensorSquare_sg25269
import Theorems.Thm_OAI_UniversalTensorSquare_sg25270
import Theorems.Thm_OAI_UniversalTensorSquare_sg25271
import Theorems.Thm_OAI_UniversalTensorSquare_sg25272
import Theorems.Thm_OAI_UniversalTensorSquare_sg25274
import Theorems.Thm_OAI_UniversalTensorSquare_sg25275
import Theorems.Thm_OAI_UniversalTensorSquare_sg25276
import Theorems.Thm_OAI_UniversalTensorSquare_sg25277
import Theorems.Thm_OAI_UniversalTensorSquare_sg25278
import Theorems.Thm_OAI_UniversalTensorSquare_sg25279
import Theorems.Thm_OAI_UniversalTensorSquare_sg25280
import Theorems.Thm_OAI_UniversalTensorSquare_sg25281
import Theorems.Thm_OAI_UniversalTensorSquare_sg25283
import Theorems.Thm_OAI_UniversalTensorSquare_sg25284
import Theorems.Thm_OAI_UniversalTensorSquare_sg25285
import Theorems.Thm_OAI_UniversalTensorSquare_sg25286
import Theorems.Thm_OAI_UniversalTensorSquare_sg25288
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg5423
import Theorems.Thm_OAI_UniversalTensorSquare_sg8867
import Theorems.Thm_OAI_UniversalTensorSquare_sg9170
import Theorems.Thm_OAI_UniversalTensorSquare_sg9527
import Theorems.Thm_OAI_UniversalTensorSquare_sg9756
import Theorems.Thm_OAI_UniversalTensorSquare_sg9761

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

lemma sgCert536 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB536 sgT536) sgFlag536 = 10 := by
  decide +kernel

lemma sg536 : RowSquare [4,2,1,1,1] [2,2,2,1,1,1] := by
  apply rowSquare_compact (n := 9) (cs := [4,2,1,1,1]) (ts := [6,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB536 sgT536 sgFlag536
  change solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB536 sgT536) sgFlag536 ≠ 0
  rw [sgCert536]
  norm_num

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

lemma sg807 : RowSquare [4,2,1,1,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg178

lemma sg914 : RowSquare [5,2,1,1,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg52

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

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

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

lemma sg9001 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg914 sg1891

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

lemma sg8720 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg1327

lemma sg8825 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5423

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9756

lemma sg25263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9527

lemma sg25273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9761

lemma sg25282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8867 sg9001

lemma sg25287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8825 sg9170

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

lemma degreeTree43_125All_oai : degreeTree43_125.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25273,⟨sg25265,⟨sg25261,⟨sg25259,⟨sg25258,True.intro,True.intro⟩,⟨sg25260,True.intro,True.intro⟩⟩,⟨sg25263,⟨sg25262,True.intro,True.intro⟩,⟨sg25264,True.intro,True.intro⟩⟩⟩,⟨sg25269,⟨sg25267,⟨sg25266,True.intro,True.intro⟩,⟨sg25268,True.intro,True.intro⟩⟩,⟨sg25271,⟨sg25270,True.intro,True.intro⟩,⟨sg25272,True.intro,True.intro⟩⟩⟩⟩,⟨sg25281,⟨sg25277,⟨sg25275,⟨sg25274,True.intro,True.intro⟩,⟨sg25276,True.intro,True.intro⟩⟩,⟨sg25279,⟨sg25278,True.intro,True.intro⟩,⟨sg25280,True.intro,True.intro⟩⟩⟩,⟨sg25285,⟨sg25283,⟨sg25282,True.intro,True.intro⟩,⟨sg25284,True.intro,True.intro⟩⟩,⟨sg25287,⟨sg25286,True.intro,True.intro⟩,⟨sg25288,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_125All_oai := @OAI.UniversalTensorSquare.degreeTree43_125All_oai
