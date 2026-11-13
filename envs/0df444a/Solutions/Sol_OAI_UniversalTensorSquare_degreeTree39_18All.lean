-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_18All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:29:26.346716+00:00
-- url     : https://prove2.me/submissions/cf871fdc-e53a-4cf7-8dcf-49d90d1ec104
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21962
import Theorems.Thm_OAI_UniversalTensorSquare_sg21963
import Theorems.Thm_OAI_UniversalTensorSquare_sg21964
import Theorems.Thm_OAI_UniversalTensorSquare_sg21966
import Theorems.Thm_OAI_UniversalTensorSquare_sg21967
import Theorems.Thm_OAI_UniversalTensorSquare_sg21968
import Theorems.Thm_OAI_UniversalTensorSquare_sg21969
import Theorems.Thm_OAI_UniversalTensorSquare_sg21970
import Theorems.Thm_OAI_UniversalTensorSquare_sg21972
import Theorems.Thm_OAI_UniversalTensorSquare_sg21973
import Theorems.Thm_OAI_UniversalTensorSquare_sg21974
import Theorems.Thm_OAI_UniversalTensorSquare_sg21975
import Theorems.Thm_OAI_UniversalTensorSquare_sg21977
import Theorems.Thm_OAI_UniversalTensorSquare_sg21978
import Theorems.Thm_OAI_UniversalTensorSquare_sg21981
import Theorems.Thm_OAI_UniversalTensorSquare_sg21982
import Theorems.Thm_OAI_UniversalTensorSquare_sg21983
import Theorems.Thm_OAI_UniversalTensorSquare_sg21985
import Theorems.Thm_OAI_UniversalTensorSquare_sg21987
import Theorems.Thm_OAI_UniversalTensorSquare_sg21988
import Theorems.Thm_OAI_UniversalTensorSquare_sg21989
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6788
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7347
import Theorems.Thm_OAI_UniversalTensorSquare_sg7349
import Theorems.Thm_OAI_UniversalTensorSquare_sg7350
import Theorems.Thm_OAI_UniversalTensorSquare_sg7351
import Theorems.Thm_OAI_UniversalTensorSquare_sg7580
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

lemma sgCert814 : solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB814 sgT814) sgFlag814 = -6 := by
  decide +kernel

lemma sg814 : RowSquare [4,2,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB814 sgT814 sgFlag814
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB814 sgT814) sgFlag814 ≠ 0
  rw [sgCert814]
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

lemma sgCert275 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 = -1 := by
  decide +kernel

lemma sg275 : RowSquare [3,2,1,1,1] [3,3,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [3,2,1,1,1]) (ts := [4,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB275 sgT275 sgFlag275
  change solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 ≠ 0
  rw [sgCert275]
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

lemma sg6154 : RowSquare [5,4,3,2,1,1,1,1,1] [3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1686

lemma sg6298 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg910

lemma sg6299 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg910

lemma sg6427 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg275 sg1327

lemma sg6428 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg814

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

lemma sg21965 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7347

lemma sg21971 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7580

lemma sg21976 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7349

lemma sg21979 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6427 sg6788

lemma sg21980 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7350

lemma sg21984 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6428 sg6788

lemma sg21986 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6298 sg7351

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

lemma degreeTree39_18All_oai : degreeTree39_18.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21976,⟨sg21969,⟨sg21965,⟨sg21963,⟨sg21962,True.intro,True.intro⟩,⟨sg21964,True.intro,True.intro⟩⟩,⟨sg21967,⟨sg21966,True.intro,True.intro⟩,⟨sg21968,True.intro,True.intro⟩⟩⟩,⟨sg21973,⟨sg21971,⟨sg21970,True.intro,True.intro⟩,⟨sg21972,True.intro,True.intro⟩⟩,⟨sg21975,⟨sg21974,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21983,⟨sg21980,⟨sg21978,⟨sg21977,True.intro,True.intro⟩,⟨sg21979,True.intro,True.intro⟩⟩,⟨sg21982,⟨sg21981,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21987,⟨sg21985,⟨sg21984,True.intro,True.intro⟩,⟨sg21986,True.intro,True.intro⟩⟩,⟨sg21989,⟨sg21988,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_18All_oai := @OAI.UniversalTensorSquare.degreeTree39_18All_oai
