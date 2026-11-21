-- Prove2me | solution 1 for OAI.UniversalTensorSquare.universal_partition_le64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:07:28.576296+00:00
-- url     : https://prove2.me/submissions/5c66eccb-0072-431e-92a6-0ff222f922d8

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_residual_pos
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos11
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos12
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos13
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos14
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos16
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos18
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos19
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos20
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos22
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos24
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos26
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos31
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos32
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos33
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos34
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos35
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos37
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos38
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos39
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos41
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos43
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos44
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos46
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos48
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos50
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos52
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos53
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos54
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos56
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos57
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos58
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos59
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos60
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos61
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos62
import Theorems.Thm_OAI_UniversalTensorSquare_degree_pos64
import Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_universal_tensor_square_le_ten

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

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

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

end UniversalTensorSquare
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

lemma columnShape_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    columnShape rs = columnShape ss := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  rw [columnShape_rowLen,columnShape_rowLen,h.countP_eq]

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

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma dominates_of_rowsDom {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : RowsDom μ.rowLens θ.rowLens) : Dominates μ θ := by
  intro k
  by_cases hk : k ≤ θ.colLen 0
  · rw [rowPrefix_eq_take,rowPrefix_eq_take]
    exact h k (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  · have hh := h (θ.colLen 0) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    rw [← rowPrefix_eq_take,← rowPrefix_eq_take,rowPrefix_eq_card θ le_rfl,← hc] at hh
    rw [rowPrefix_eq_card θ (by omega),← hc]
    exact hh.trans (rowPrefix_mono μ (by omega))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma SquareOccurs.of_packing {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hh : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (hlam : lam.card = n) (hμ : μ.card = n)
    (hd : Dominates μ (rowDiagram p.parts)) : SquareOccurs lam μ := by
  exact ⟨n,canonicalTableau lam hlam,canonicalTableau μ hμ,
    packingPlan_pos p hv hb hh hc hp _ _ hd⟩

end UniversalTensorSquare

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma candidate_cone {n M b δ : ℕ} (hM : 4 ≤ M)
    (hn : (candidate M b δ).card = n) (p : PackingPlan) (q : List ℕ)
    (hq : GoodRows q) (hqn : q.sum = n)
    (hv : p.Valid (M+b+δ)) (hb : BandsValid p.bands)
    (hc : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hp : p.parts.Perm q) (μ : YoungDiagram) (hμ : μ.card = n)
    (hd : RowsDom μ.rowLens q) : SquareOccurs (candidate M b δ) μ := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  apply SquareOccurs.of_packing p hv hb hh
  · rw [candidate_transpose,candidate_rowLens hM]; exact hc
  · exact fun a ha => hq.2 a (hp.mem_iff.mp ha)
  · exact hn
  · exact hμ
  · have he : rowDiagram p.parts = rowDiagram q := by
      unfold rowDiagram; rw [columnShape_perm hp]
    rw [he]
    apply dominates_of_rowsDom
    · rw [rowDiagram_card,hqn,hμ]
    · simpa only [rowDiagram_rows hq] using hd

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones17 : ∀ q ∈ degreeQs17, ∀ μ : YoungDiagram, μ.card = 17 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 5 0 1) μ := by
  intro q hq
  simp only [degreeQs17,List.not_mem_nil] at hq

lemma degreeCheck17_0_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 (d+1) (e+1) (a+1) (c+1) degreeRows17_0 degreeP17 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck17_0_0
  · exact degreeCheck17_0_1
  · exact degreeCheck17_0_2
  · exact degreeCheck17_0_3
  · exact degreeCheck17_0_4
  · exact degreeCheck17_1_0
  · exact degreeCheck17_1_1
  · exact degreeCheck17_1_2
  · exact degreeCheck17_1_3
  · exact degreeCheck17_1_4
  · exact degreeCheck17_2_0
  · exact degreeCheck17_2_1
  · exact degreeCheck17_2_2
  · exact degreeCheck17_2_3
  · exact degreeCheck17_2_4
  · exact degreeCheck17_3_0
  · exact degreeCheck17_3_1
  · exact degreeCheck17_3_2
  · exact degreeCheck17_3_3
  · exact degreeCheck17_3_4
  · exact degreeCheck17_4_0
  · exact degreeCheck17_4_1
  · exact degreeCheck17_4_2
  · exact degreeCheck17_4_3
  · exact degreeCheck17_4_4

lemma degree_pos17 (μ : YoungDiagram) (hμ : μ.card = 17) :
    0 < kronecker (canonicalTableau (candidate 5 0 1) degreeCard17)
      (canonicalTableau (candidate 5 0 1) degreeCard17) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard17 degreeRows17_0 (by decide) (by decide)
    degreePlan17_0 (by decide) (by decide) (by decide) (by decide) degreeP17 ?_
    degreeCheck17 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard17 rfl degreeCones17
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCone23_1 (μ : YoungDiagram) (hμ : μ.card = 23)
    (hd : RowsDom μ.rowLens degreeRows23_1) : SquareOccurs (candidate 6 0 1) μ := by
  exact candidate_cone (by decide) degreeCard23 degreePlan23_1 degreeRows23_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

lemma degreeCones23 : ∀ q ∈ degreeQs23, ∀ μ : YoungDiagram, μ.card = 23 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 0 1) μ := by
  intro q hq
  simp only [degreeQs23,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone23_1

lemma degreeCheck23_0_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 (d+1) (e+1) (a+1) (c+1) degreeRows23_0 degreeP23 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck23_0_0
  · exact degreeCheck23_0_1
  · exact degreeCheck23_0_2
  · exact degreeCheck23_0_3
  · exact degreeCheck23_0_4
  · exact degreeCheck23_1_0
  · exact degreeCheck23_1_1
  · exact degreeCheck23_1_2
  · exact degreeCheck23_1_3
  · exact degreeCheck23_1_4
  · exact degreeCheck23_2_0
  · exact degreeCheck23_2_1
  · exact degreeCheck23_2_2
  · exact degreeCheck23_2_3
  · exact degreeCheck23_2_4
  · exact degreeCheck23_3_0
  · exact degreeCheck23_3_1
  · exact degreeCheck23_3_2
  · exact degreeCheck23_3_3
  · exact degreeCheck23_3_4
  · exact degreeCheck23_4_0
  · exact degreeCheck23_4_1
  · exact degreeCheck23_4_2
  · exact degreeCheck23_4_3
  · exact degreeCheck23_4_4

lemma degree_pos23 (μ : YoungDiagram) (hμ : μ.card = 23) :
    0 < kronecker (canonicalTableau (candidate 6 0 1) degreeCard23)
      (canonicalTableau (candidate 6 0 1) degreeCard23) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard23 degreeRows23_0 (by decide) (by decide)
    degreePlan23_0 (by decide) (by decide) (by decide) (by decide) degreeP23 ?_
    degreeCheck23 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard23 rfl degreeCones23
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones25 : ∀ q ∈ degreeQs25, ∀ μ : YoungDiagram, μ.card = 25 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 1 0) μ := by
  intro q hq
  simp only [degreeQs25,List.not_mem_nil] at hq

lemma degreeCheck25_0_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 (d+1) (e+1) (a+1) (c+1) degreeRows25_0 degreeP25 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck25_0_0
  · exact degreeCheck25_0_1
  · exact degreeCheck25_0_2
  · exact degreeCheck25_0_3
  · exact degreeCheck25_0_4
  · exact degreeCheck25_1_0
  · exact degreeCheck25_1_1
  · exact degreeCheck25_1_2
  · exact degreeCheck25_1_3
  · exact degreeCheck25_1_4
  · exact degreeCheck25_2_0
  · exact degreeCheck25_2_1
  · exact degreeCheck25_2_2
  · exact degreeCheck25_2_3
  · exact degreeCheck25_2_4
  · exact degreeCheck25_3_0
  · exact degreeCheck25_3_1
  · exact degreeCheck25_3_2
  · exact degreeCheck25_3_3
  · exact degreeCheck25_3_4
  · exact degreeCheck25_4_0
  · exact degreeCheck25_4_1
  · exact degreeCheck25_4_2
  · exact degreeCheck25_4_3
  · exact degreeCheck25_4_4

lemma degree_pos25 (μ : YoungDiagram) (hμ : μ.card = 25) :
    0 < kronecker (canonicalTableau (candidate 6 1 0) degreeCard25)
      (canonicalTableau (candidate 6 1 0) degreeCard25) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard25 degreeRows25_0 (by decide) (by decide)
    degreePlan25_0 (by decide) (by decide) (by decide) (by decide) degreeP25 ?_
    degreeCheck25 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard25 rfl degreeCones25
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones27 : ∀ q ∈ degreeQs27, ∀ μ : YoungDiagram, μ.card = 27 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 1 1) μ := by
  intro q hq
  simp only [degreeQs27,List.not_mem_nil] at hq

lemma degreeCheck27_0_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 (d+1) (e+1) (a+1) (c+1) degreeRows27_0 degreeP27 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck27_0_0
  · exact degreeCheck27_0_1
  · exact degreeCheck27_0_2
  · exact degreeCheck27_0_3
  · exact degreeCheck27_0_4
  · exact degreeCheck27_1_0
  · exact degreeCheck27_1_1
  · exact degreeCheck27_1_2
  · exact degreeCheck27_1_3
  · exact degreeCheck27_1_4
  · exact degreeCheck27_2_0
  · exact degreeCheck27_2_1
  · exact degreeCheck27_2_2
  · exact degreeCheck27_2_3
  · exact degreeCheck27_2_4
  · exact degreeCheck27_3_0
  · exact degreeCheck27_3_1
  · exact degreeCheck27_3_2
  · exact degreeCheck27_3_3
  · exact degreeCheck27_3_4
  · exact degreeCheck27_4_0
  · exact degreeCheck27_4_1
  · exact degreeCheck27_4_2
  · exact degreeCheck27_4_3
  · exact degreeCheck27_4_4

lemma degree_pos27 (μ : YoungDiagram) (hμ : μ.card = 27) :
    0 < kronecker (canonicalTableau (candidate 6 1 1) degreeCard27)
      (canonicalTableau (candidate 6 1 1) degreeCard27) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard27 degreeRows27_0 (by decide) (by decide)
    degreePlan27_0 (by decide) (by decide) (by decide) (by decide) degreeP27 ?_
    degreeCheck27 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard27 rfl degreeCones27
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones29 : ∀ q ∈ degreeQs29, ∀ μ : YoungDiagram, μ.card = 29 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 2 0) μ := by
  intro q hq
  simp only [degreeQs29,List.not_mem_nil] at hq

lemma degreeCheck29_0_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 (d+1) (e+1) (a+1) (c+1) degreeRows29_0 degreeP29 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck29_0_0
  · exact degreeCheck29_0_1
  · exact degreeCheck29_0_2
  · exact degreeCheck29_0_3
  · exact degreeCheck29_0_4
  · exact degreeCheck29_1_0
  · exact degreeCheck29_1_1
  · exact degreeCheck29_1_2
  · exact degreeCheck29_1_3
  · exact degreeCheck29_1_4
  · exact degreeCheck29_2_0
  · exact degreeCheck29_2_1
  · exact degreeCheck29_2_2
  · exact degreeCheck29_2_3
  · exact degreeCheck29_2_4
  · exact degreeCheck29_3_0
  · exact degreeCheck29_3_1
  · exact degreeCheck29_3_2
  · exact degreeCheck29_3_3
  · exact degreeCheck29_3_4
  · exact degreeCheck29_4_0
  · exact degreeCheck29_4_1
  · exact degreeCheck29_4_2
  · exact degreeCheck29_4_3
  · exact degreeCheck29_4_4

lemma degree_pos29 (μ : YoungDiagram) (hμ : μ.card = 29) :
    0 < kronecker (canonicalTableau (candidate 6 2 0) degreeCard29)
      (canonicalTableau (candidate 6 2 0) degreeCard29) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard29 degreeRows29_0 (by decide) (by decide)
    degreePlan29_0 (by decide) (by decide) (by decide) (by decide) degreeP29 ?_
    degreeCheck29 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard29 rfl degreeCones29
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones30 : ∀ q ∈ degreeQs30, ∀ μ : YoungDiagram, μ.card = 30 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 7 0 1) μ := by
  intro q hq
  simp only [degreeQs30,List.not_mem_nil] at hq

lemma degreeCheck30_0_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 (d+1) (e+1) (a+1) (c+1) degreeRows30_0 degreeP30 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck30_0_0
  · exact degreeCheck30_0_1
  · exact degreeCheck30_0_2
  · exact degreeCheck30_0_3
  · exact degreeCheck30_0_4
  · exact degreeCheck30_1_0
  · exact degreeCheck30_1_1
  · exact degreeCheck30_1_2
  · exact degreeCheck30_1_3
  · exact degreeCheck30_1_4
  · exact degreeCheck30_2_0
  · exact degreeCheck30_2_1
  · exact degreeCheck30_2_2
  · exact degreeCheck30_2_3
  · exact degreeCheck30_2_4
  · exact degreeCheck30_3_0
  · exact degreeCheck30_3_1
  · exact degreeCheck30_3_2
  · exact degreeCheck30_3_3
  · exact degreeCheck30_3_4
  · exact degreeCheck30_4_0
  · exact degreeCheck30_4_1
  · exact degreeCheck30_4_2
  · exact degreeCheck30_4_3
  · exact degreeCheck30_4_4

lemma degree_pos30 (μ : YoungDiagram) (hμ : μ.card = 30) :
    0 < kronecker (canonicalTableau (candidate 7 0 1) degreeCard30)
      (canonicalTableau (candidate 7 0 1) degreeCard30) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard30 degreeRows30_0 (by decide) (by decide)
    degreePlan30_0 (by decide) (by decide) (by decide) (by decide) degreeP30 ?_
    degreeCheck30 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard30 rfl degreeCones30
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones40 : ∀ q ∈ degreeQs40, ∀ μ : YoungDiagram, μ.card = 40 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 1 0) μ := by
  intro q hq
  simp only [degreeQs40, List.not_mem_nil] at hq

lemma degreeCheck40_0_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 (d+1) (e+1) (a+1) (c+1) degreeRows40_0 degreeP40 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck40_0_0
  · exact degreeCheck40_0_1
  · exact degreeCheck40_0_2
  · exact degreeCheck40_0_3
  · exact degreeCheck40_0_4
  · exact degreeCheck40_1_0
  · exact degreeCheck40_1_1
  · exact degreeCheck40_1_2
  · exact degreeCheck40_1_3
  · exact degreeCheck40_1_4
  · exact degreeCheck40_2_0
  · exact degreeCheck40_2_1
  · exact degreeCheck40_2_2
  · exact degreeCheck40_2_3
  · exact degreeCheck40_2_4
  · exact degreeCheck40_3_0
  · exact degreeCheck40_3_1
  · exact degreeCheck40_3_2
  · exact degreeCheck40_3_3
  · exact degreeCheck40_3_4
  · exact degreeCheck40_4_0
  · exact degreeCheck40_4_1
  · exact degreeCheck40_4_2
  · exact degreeCheck40_4_3
  · exact degreeCheck40_4_4

lemma degree_pos40 (μ : YoungDiagram) (hμ : μ.card = 40) :
    0 < kronecker (canonicalTableau (candidate 8 1 0) degreeCard40)
      (canonicalTableau (candidate 8 1 0) degreeCard40) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard40 degreeRows40_0 (by decide) (by decide)
    degreePlan40_0 (by decide) (by decide) (by decide) (by decide) degreeP40 ?_
    degreeCheck40 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard40 rfl degreeCones40
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones42 : ∀ q ∈ degreeQs42, ∀ μ : YoungDiagram, μ.card = 42 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 1 1) μ := by
  intro q hq
  simp only [degreeQs42,List.not_mem_nil] at hq

lemma degreeCheck42_0_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 (d+1) (e+1) (a+1) (c+1) degreeRows42_0 degreeP42 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck42_0_0
  · exact degreeCheck42_0_1
  · exact degreeCheck42_0_2
  · exact degreeCheck42_0_3
  · exact degreeCheck42_0_4
  · exact degreeCheck42_1_0
  · exact degreeCheck42_1_1
  · exact degreeCheck42_1_2
  · exact degreeCheck42_1_3
  · exact degreeCheck42_1_4
  · exact degreeCheck42_2_0
  · exact degreeCheck42_2_1
  · exact degreeCheck42_2_2
  · exact degreeCheck42_2_3
  · exact degreeCheck42_2_4
  · exact degreeCheck42_3_0
  · exact degreeCheck42_3_1
  · exact degreeCheck42_3_2
  · exact degreeCheck42_3_3
  · exact degreeCheck42_3_4
  · exact degreeCheck42_4_0
  · exact degreeCheck42_4_1
  · exact degreeCheck42_4_2
  · exact degreeCheck42_4_3
  · exact degreeCheck42_4_4

lemma degree_pos42 (μ : YoungDiagram) (hμ : μ.card = 42) :
    0 < kronecker (canonicalTableau (candidate 8 1 1) degreeCard42)
      (canonicalTableau (candidate 8 1 1) degreeCard42) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard42 degreeRows42_0 (by decide) (by decide)
    degreePlan42_0 (by decide) (by decide) (by decide) (by decide) degreeP42 ?_
    degreeCheck42 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard42 rfl degreeCones42
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones47 : ∀ q ∈ degreeQs47, ∀ μ : YoungDiagram, μ.card = 47 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 0 1) μ := by
  intro q hq
  simp only [degreeQs47, List.not_mem_nil] at hq

lemma degreeCheck47_0_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 (d+1) (e+1) (a+1) (c+1) degreeRows47_0 degreeP47 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck47_0_0
  · exact degreeCheck47_0_1
  · exact degreeCheck47_0_2
  · exact degreeCheck47_0_3
  · exact degreeCheck47_0_4
  · exact degreeCheck47_1_0
  · exact degreeCheck47_1_1
  · exact degreeCheck47_1_2
  · exact degreeCheck47_1_3
  · exact degreeCheck47_1_4
  · exact degreeCheck47_2_0
  · exact degreeCheck47_2_1
  · exact degreeCheck47_2_2
  · exact degreeCheck47_2_3
  · exact degreeCheck47_2_4
  · exact degreeCheck47_3_0
  · exact degreeCheck47_3_1
  · exact degreeCheck47_3_2
  · exact degreeCheck47_3_3
  · exact degreeCheck47_3_4
  · exact degreeCheck47_4_0
  · exact degreeCheck47_4_1
  · exact degreeCheck47_4_2
  · exact degreeCheck47_4_3
  · exact degreeCheck47_4_4

lemma degree_pos47 (μ : YoungDiagram) (hμ : μ.card = 47) :
    0 < kronecker (canonicalTableau (candidate 9 0 1) degreeCard47)
      (canonicalTableau (candidate 9 0 1) degreeCard47) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard47 degreeRows47_0 (by decide) (by decide)
    degreePlan47_0 (by decide) (by decide) (by decide) (by decide) degreeP47 ?_
    degreeCheck47 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard47 rfl degreeCones47
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones49 : ∀ q ∈ degreeQs49, ∀ μ : YoungDiagram, μ.card = 49 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 1 0) μ := by
  intro q hq
  simp only [degreeQs49,List.not_mem_nil] at hq

lemma degreeCheck49_0_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 (d+1) (e+1) (a+1) (c+1) degreeRows49_0 degreeP49 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck49_0_0
  · exact degreeCheck49_0_1
  · exact degreeCheck49_0_2
  · exact degreeCheck49_0_3
  · exact degreeCheck49_0_4
  · exact degreeCheck49_1_0
  · exact degreeCheck49_1_1
  · exact degreeCheck49_1_2
  · exact degreeCheck49_1_3
  · exact degreeCheck49_1_4
  · exact degreeCheck49_2_0
  · exact degreeCheck49_2_1
  · exact degreeCheck49_2_2
  · exact degreeCheck49_2_3
  · exact degreeCheck49_2_4
  · exact degreeCheck49_3_0
  · exact degreeCheck49_3_1
  · exact degreeCheck49_3_2
  · exact degreeCheck49_3_3
  · exact degreeCheck49_3_4
  · exact degreeCheck49_4_0
  · exact degreeCheck49_4_1
  · exact degreeCheck49_4_2
  · exact degreeCheck49_4_3
  · exact degreeCheck49_4_4

lemma degree_pos49 (μ : YoungDiagram) (hμ : μ.card = 49) :
    0 < kronecker (canonicalTableau (candidate 9 1 0) degreeCard49)
      (canonicalTableau (candidate 9 1 0) degreeCard49) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard49 degreeRows49_0 (by decide) (by decide)
    degreePlan49_0 (by decide) (by decide) (by decide) (by decide) degreeP49 ?_
    degreeCheck49 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard49 rfl degreeCones49
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones51 : ∀ q ∈ degreeQs51, ∀ μ : YoungDiagram, μ.card = 51 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 1 1) μ := by
  intro q hq
  simp only [degreeQs51,List.not_mem_nil] at hq

lemma degreeCheck51_0_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 (d+1) (e+1) (a+1) (c+1) degreeRows51_0 degreeP51 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck51_0_0
  · exact degreeCheck51_0_1
  · exact degreeCheck51_0_2
  · exact degreeCheck51_0_3
  · exact degreeCheck51_0_4
  · exact degreeCheck51_1_0
  · exact degreeCheck51_1_1
  · exact degreeCheck51_1_2
  · exact degreeCheck51_1_3
  · exact degreeCheck51_1_4
  · exact degreeCheck51_2_0
  · exact degreeCheck51_2_1
  · exact degreeCheck51_2_2
  · exact degreeCheck51_2_3
  · exact degreeCheck51_2_4
  · exact degreeCheck51_3_0
  · exact degreeCheck51_3_1
  · exact degreeCheck51_3_2
  · exact degreeCheck51_3_3
  · exact degreeCheck51_3_4
  · exact degreeCheck51_4_0
  · exact degreeCheck51_4_1
  · exact degreeCheck51_4_2
  · exact degreeCheck51_4_3
  · exact degreeCheck51_4_4

lemma degree_pos51 (μ : YoungDiagram) (hμ : μ.card = 51) :
    0 < kronecker (canonicalTableau (candidate 9 1 1) degreeCard51)
      (canonicalTableau (candidate 9 1 1) degreeCard51) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard51 degreeRows51_0 (by decide) (by decide)
    degreePlan51_0 (by decide) (by decide) (by decide) (by decide) degreeP51 ?_
    degreeCheck51 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard51 rfl degreeCones51
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones63 : ∀ q ∈ degreeQs63, ∀ μ : YoungDiagram, μ.card = 63 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 2 0) μ := by
  intro q hq
  simp only [degreeQs63, List.not_mem_nil] at hq

lemma degreeCheck63_0_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 (d+1) (e+1) (a+1) (c+1) degreeRows63_0 degreeP63 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck63_0_0
  · exact degreeCheck63_0_1
  · exact degreeCheck63_0_2
  · exact degreeCheck63_0_3
  · exact degreeCheck63_0_4
  · exact degreeCheck63_1_0
  · exact degreeCheck63_1_1
  · exact degreeCheck63_1_2
  · exact degreeCheck63_1_3
  · exact degreeCheck63_1_4
  · exact degreeCheck63_2_0
  · exact degreeCheck63_2_1
  · exact degreeCheck63_2_2
  · exact degreeCheck63_2_3
  · exact degreeCheck63_2_4
  · exact degreeCheck63_3_0
  · exact degreeCheck63_3_1
  · exact degreeCheck63_3_2
  · exact degreeCheck63_3_3
  · exact degreeCheck63_3_4
  · exact degreeCheck63_4_0
  · exact degreeCheck63_4_1
  · exact degreeCheck63_4_2
  · exact degreeCheck63_4_3
  · exact degreeCheck63_4_4

lemma degree_pos63 (μ : YoungDiagram) (hμ : μ.card = 63) :
    0 < kronecker (canonicalTableau (candidate 10 2 0) degreeCard63)
      (canonicalTableau (candidate 10 2 0) degreeCard63) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard63 degreeRows63_0 (by decide) (by decide)
    degreePlan63_0 (by decide) (by decide) (by decide) (by decide) degreeP63 ?_
    degreeCheck63 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard63 rfl degreeCones63
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Universal tensor squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma universal_partition_le64_oai (n : ℕ) (hn : 0 < n)
    (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) (hsmall : n ≤ 64) :
    ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
  by_cases hten : n ≤ 10
  · obtain ⟨lam,hc,hpos,_⟩ := universal_tensor_square_le_ten.{0} n hn h2 h4 h9 hten
    exact ⟨lam,hc,hpos⟩
  have hlo : 11 ≤ n := by omega
  interval_cases n
  · exact ⟨_,degreeCard11,degree_pos11⟩
  · exact ⟨_,degreeCard12,degree_pos12⟩
  · exact ⟨_,degreeCard13,degree_pos13⟩
  · exact ⟨_,degreeCard14,degree_pos14⟩
  · exact ⟨staircase 5,staircase_card 5,saxl_kronecker_pos 5 (by decide)⟩
  · exact ⟨_,degreeCard16,degree_pos16⟩
  · exact ⟨_,degreeCard17,degree_pos17⟩
  · exact ⟨_,degreeCard18,degree_pos18⟩
  · exact ⟨_,degreeCard19,degree_pos19⟩
  · exact ⟨_,degreeCard20,degree_pos20⟩
  · exact ⟨staircase 6,staircase_card 6,saxl_kronecker_pos 6 (by decide)⟩
  · exact ⟨_,degreeCard22,degree_pos22⟩
  · exact ⟨_,degreeCard23,degree_pos23⟩
  · exact ⟨_,degreeCard24,degree_pos24⟩
  · exact ⟨_,degreeCard25,degree_pos25⟩
  · exact ⟨_,degreeCard26,degree_pos26⟩
  · exact ⟨_,degreeCard27,degree_pos27⟩
  · exact ⟨staircase 7,staircase_card 7,saxl_kronecker_pos 7 (by decide)⟩
  · exact ⟨_,degreeCard29,degree_pos29⟩
  · exact ⟨_,degreeCard30,degree_pos30⟩
  · exact ⟨_,degreeCard31,degree_pos31⟩
  · exact ⟨_,degreeCard32,degree_pos32⟩
  · exact ⟨_,degreeCard33,degree_pos33⟩
  · exact ⟨_,degreeCard34,degree_pos34⟩
  · exact ⟨_,degreeCard35,degree_pos35⟩
  · exact ⟨staircase 8,staircase_card 8,saxl_kronecker_pos 8 (by decide)⟩
  · exact ⟨_,degreeCard37,degree_pos37⟩
  · exact ⟨_,degreeCard38,degree_pos38⟩
  · exact ⟨_,degreeCard39,degree_pos39⟩
  · exact ⟨_,degreeCard40,degree_pos40⟩
  · exact ⟨_,degreeCard41,degree_pos41⟩
  · exact ⟨_,degreeCard42,degree_pos42⟩
  · exact ⟨_,degreeCard43,degree_pos43⟩
  · exact ⟨_,degreeCard44,degree_pos44⟩
  · exact ⟨staircase 9,staircase_card 9,saxl_kronecker_pos 9 (by decide)⟩
  · exact ⟨_,degreeCard46,degree_pos46⟩
  · exact ⟨_,degreeCard47,degree_pos47⟩
  · exact ⟨_,degreeCard48,degree_pos48⟩
  · exact ⟨_,degreeCard49,degree_pos49⟩
  · exact ⟨_,degreeCard50,degree_pos50⟩
  · exact ⟨_,degreeCard51,degree_pos51⟩
  · exact ⟨_,degreeCard52,degree_pos52⟩
  · exact ⟨_,degreeCard53,degree_pos53⟩
  · exact ⟨_,degreeCard54,degree_pos54⟩
  · exact ⟨staircase 10,staircase_card 10,saxl_kronecker_pos 10 (by decide)⟩
  · exact ⟨_,degreeCard56,degree_pos56⟩
  · exact ⟨_,degreeCard57,degree_pos57⟩
  · exact ⟨_,degreeCard58,degree_pos58⟩
  · exact ⟨_,degreeCard59,degree_pos59⟩
  · exact ⟨_,degreeCard60,degree_pos60⟩
  · exact ⟨_,degreeCard61,degree_pos61⟩
  · exact ⟨_,degreeCard62,degree_pos62⟩
  · exact ⟨_,degreeCard63,degree_pos63⟩
  · exact ⟨_,degreeCard64,degree_pos64⟩

universe u

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.universal_partition_le64_oai := @OAI.UniversalTensorSquare.universal_partition_le64_oai
