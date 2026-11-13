-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeCheck116
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:20.333377+00:00
-- url     : https://prove2.me/submissions/24f4c6e1-796f-40d7-adeb-022d2ce0f34a

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

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

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

open scoped MonoidAlgebra

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceDominance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Dominance. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl

lemma colPrefix_eq_min_sum (μ : YoungDiagram) (k : ℕ) :
    colPrefix μ k = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
  rw [← colTruncate_card, ← rowPrefix_eq_card _ (colTruncate_height μ k)]
  exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
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

lemma rowLen_first_le_prefix (μ : YoungDiagram) {i : ℕ} (hi : 0 < i) :
    μ.rowLen 0 ≤ rowPrefix μ i := by
  have h := rowPrefix_mono μ (show 1 ≤ i from hi)
  simpa [rowPrefix] using h

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Rows. -/

section

namespace UniversalTensorSquare

lemma list_sum_le_mul_length {rs : List ℕ} {b : ℕ} (h : ∀ a ∈ rs, a ≤ b) :
    rs.sum ≤ rs.length*b := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    have ha := h a (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma clippedSum_length_le {rs : List ℕ} (hp : ∀ a ∈ rs, 0 < a) {k : ℕ} (hk : 0 < k) :
    rs.length ≤ clippedSum rs k := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hp a (by simp)
    have ht := ih (fun x hx => hp x (by simp [hx]))
    simp only [clippedSum,List.map_cons,List.sum_cons,List.length_cons] at *
    have : 1 ≤ min k a := le_min hk ha
    omega

lemma clippedSum_proportion {rs : List ℕ} {upper k : ℕ}
    (hu : ∀ a ∈ rs, a ≤ upper) : rs.sum * min k upper ≤ clippedSum rs k * upper := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hu a (by simp)
    have ht := ih (fun x hx => hu x (by simp [hx]))
    have hm : a * min k upper ≤ min k a * upper := by
      by_cases hk : k ≤ a
      · rw [min_eq_left hk, min_eq_left (hk.trans ha)]
        exact Nat.mul_le_mul_right k ha |>.trans_eq (Nat.mul_comm upper k)
      · rw [min_eq_right (by omega : a ≤ k)]
        exact Nat.mul_le_mul_left a (min_le_right _ _)
    simp only [clippedSum,List.map_cons,List.sum_cons] at *
    nlinarith

lemma cross_product_bound (xs ys : List ℕ)
    (h : ∀ a ∈ xs, ∀ b ∈ ys, b ≤ a) : ys.sum*xs.length ≤ xs.sum*ys.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := list_sum_le_mul_length (fun b hb => h a (by simp) b hb)
    have ht := ih (fun c hc b hb => h c (by simp [hc]) b hb)
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma rowSum_proportion {rs : List ℕ} (hs : rs.SortedGE) (k : ℕ) :
    rs.sum * min k rs.length ≤ (rs.take k).sum * rs.length := by
  have he : (rs.take k ++ rs.drop k).Pairwise (· ≥ ·) := by
    simpa only [List.take_append_drop] using hs.pairwise
  have hh := cross_product_bound (rs.take k) (rs.drop k) (List.pairwise_append.mp he).2.2
  have hl : (rs.take k).length + (rs.drop k).length = rs.length := by
    rw [← List.length_append,List.take_append_drop]
  have ht : (rs.take k).sum + (rs.drop k).sum = rs.sum := by
    rw [← List.sum_append,List.take_append_drop]
  rw [List.length_take] at hh hl
  calc
    rs.sum * min k rs.length = ((rs.take k).sum + (rs.drop k).sum)*min k rs.length := by rw [ht]
    _ = (rs.take k).sum*min k rs.length + (rs.drop k).sum*min k rs.length := by ring
    _ ≤ (rs.take k).sum*min k rs.length + (rs.take k).sum*(rs.drop k).length := Nat.add_le_add_left hh _
    _ = (rs.take k).sum*(min k rs.length+(rs.drop k).length) := by ring
    _ = _ := by rw [hl]

lemma rejectedRows_false {rs : List ℕ} {fuel n upper : ℕ} {A B : List (ℕ × ℕ)}
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    ¬rejectedRows fuel n upper A B := by
  intro hh
  have hlo : fuel ≤ n := by
    rw [← hlen,← hsum]
    exact List.length_le_sum_of_one_le _ hp
  have hhi : n ≤ fuel*upper := by rw [← hsum,← hlen]; exact list_sum_le_mul_length hu
  rcases hh with h | h | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpU⟩ | ⟨p,hp',hpU⟩
  · omega
  · omega
  · have hw := (clippedSum_length_le hp hpk).trans (ha p hp')
    omega
  · have hw := hb p hp'
    rw [List.take_of_length_le (hlen ▸ hpk),hsum] at hw
    omega
  · have hh := (clippedSum_proportion (k := p.1) hu).trans
      (Nat.mul_le_mul_right upper (ha p hp'))
    rw [hsum] at hh
    omega
  · have hh := (rowSum_proportion hs p.1).trans (Nat.mul_le_mul_right rs.length (hb p hp'))
    rw [hsum,hlen] at hh
    omega

lemma allowedRow_cons {a : ℕ} {rs : List ℕ} {A B : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) (hb : ListRowBounds (a::rs) B) :
    allowedRow a A B := by
  constructor
  · intro p hp
    have hh := ha p hp
    simp only [clippedSum,List.map_cons,List.sum_cons] at hh
    omega
  · intro p hp hk
    have hh := hb p hp
    obtain ⟨k,hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.1 ≠ 0)
    simp only [hk',List.take_succ_cons,List.sum_cons] at hh
    omega

lemma clipBudget_cons {a : ℕ} {rs : List ℕ} {A : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) : ListColBounds rs (clipBudget A a) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hh := ha q hq
  simp only [clippedSum,List.map_cons,List.sum_cons] at hh ⊢
  omega

lemma rowBudget_cons {a : ℕ} {rs : List ℕ} {B : List (ℕ × ℕ)}
    (hb : ListRowBounds (a::rs) B) : ListRowBounds rs (rowBudget B a) := by
  intro p hp
  obtain ⟨q,hq,he⟩ := List.mem_filterMap.mp hp
  split_ifs at he with hk
  · have hh := hb q hq
    have heq := Option.some.inj he
    subst p
    have ht : q.1 = (q.1-1)+1 := by omega
    rw [ht,List.take_succ_cons,List.sum_cons] at hh
    dsimp only
    omega

lemma mem_constrainedRows (fuel : ℕ) (rs : List ℕ) (n upper : ℕ) (A B : List (ℕ × ℕ))
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    rs ∈ constrainedRows fuel n upper A B := by
  have hr := rejectedRows_false hlen hsum hp hu hs ha hb
  induction fuel generalizing rs n upper A B with
  | zero =>
    have he : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [constrainedRows,hr]
  | succ fuel ih =>
    cases rs with
    | nil => simp at hlen
    | cons a rs =>
      rw [constrainedRows,ite_eq_right hr]
      apply List.mem_flatMap.mpr
      have hap := hp a (by simp)
      have hau := hu a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      refine ⟨a,?_,?_⟩
      · simp only [List.mem_range'_1]
        omega
      · have haall : ∀ x ∈ a::rs, x ≤ a := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact (List.pairwise_cons.mp hs.pairwise).1 x hx
        have hlim : n ≤ (fuel+1)*a := by
          have hh := list_sum_le_mul_length haall
          rw [hsum,hlen] at hh
          exact hh
        rw [ite_eq_left ⟨allowedRow_cons ha hb,hlim⟩]
        apply List.mem_map.mpr
        refine ⟨rs,ih rs (n-a) a (clipBudget A a) (rowBudget B a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,rfl⟩
        · simpa only [List.length_cons,Nat.succ.injEq] using hlen
        · simp only [List.sum_cons] at hsum; omega
        · exact fun x hx => hp x (by simp [hx])
        · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
        · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
        · exact clipBudget_cons ha
        · exact rowBudget_cons hb
        · apply rejectedRows_false
          · simpa only [List.length_cons,Nat.succ.injEq] using hlen
          · simp only [List.sum_cons] at hsum; omega
          · exact fun x hx => hp x (by simp [hx])
          · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
          · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
          · exact clipBudget_cons ha
          · exact rowBudget_cons hb

end UniversalTensorSquare
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

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Diagrams. -/

section

namespace UniversalTensorSquare
open Saxl

lemma firstBound_sound {n : ℕ} (μ : YoungDiagram) (hc : μ.card = n)
    {B : List (ℕ × ℕ)} (hb : RowBounds μ B) : μ.rowLen 0 ≤ firstBound n B := by
  induction B with
  | nil =>
    have hh := rowPrefix_le_card μ 1
    simpa [firstBound,rowPrefix,hc] using hh
  | cons p B ih =>
    have hp := hb p (by simp)
    simp only [firstBound,List.foldr_cons,ite_eq_left hp.1]
    exact le_min ((rowLen_first_le_prefix μ hp.1).trans hp.2)
      (ih (fun q hq => hb q (by simp [hq])))

lemma clippedSum_rowLens (μ : YoungDiagram) (k : ℕ) :
    clippedSum μ.rowLens k = colPrefix μ k := by
  rw [colPrefix_eq_min_sum]
  rw [YoungDiagram.rowLens]
  simp only [clippedSum,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

end UniversalTensorSquare
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

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma boundsEntail_sound {A B : List (ℕ × ℕ)} (h : boundsEntail A B)
    (μ : YoungDiagram) (ha : RowBounds μ A) : RowBounds μ B := by
  intro p hp
  obtain ⟨hpos,q,hq,hk,hv⟩ := h p hp
  exact ⟨hpos,((rowPrefix_mono μ hk).trans (ha q hq).2).trans hv⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover116_0_0 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 1 1 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_0_1 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 1 2 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_0_2 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 1 3 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_0_3 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 1 4 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_0_4 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 1 5 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_1_0 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 2 1 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_1_1 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 2 2 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_1_2 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 2 3 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_1_3 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 2 4 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_1_4 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 2 5 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_2_0 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 3 1 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_2_1 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 3 2 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_2_2 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 3 3 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_2_3 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 3 4 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_2_4 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 3 5 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_3_0 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 4 1 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_3_1 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 4 2 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_3_2 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 4 3 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_3_3 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 4 4 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_3_4 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 4 5 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_4_0 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 5 1 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_4_1 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 5 2 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_4_2 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 5 3 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_4_3 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 5 4 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116_4_4 :
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 5 5 (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  decide +kernel

lemma degreeCover116 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      regionCheck 116 12 19 (d+1) (e+1) (a+1) (c+1) degreeRows116_0 degreeRegions116 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover116_0_0
  · exact degreeCover116_0_1
  · exact degreeCover116_0_2
  · exact degreeCover116_0_3
  · exact degreeCover116_0_4
  · exact degreeCover116_1_0
  · exact degreeCover116_1_1
  · exact degreeCover116_1_2
  · exact degreeCover116_1_3
  · exact degreeCover116_1_4
  · exact degreeCover116_2_0
  · exact degreeCover116_2_1
  · exact degreeCover116_2_2
  · exact degreeCover116_2_3
  · exact degreeCover116_2_4
  · exact degreeCover116_3_0
  · exact degreeCover116_3_1
  · exact degreeCover116_3_2
  · exact degreeCover116_3_3
  · exact degreeCover116_3_4
  · exact degreeCover116_4_0
  · exact degreeCover116_4_1
  · exact degreeCover116_4_2
  · exact degreeCover116_4_3
  · exact degreeCover116_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 116. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight116 : ∀ R ∈ degreeHalfRegions116, firstBound 116 R.1 ≤ 22 := by decide +kernel

lemma degreeHalfWidth116 : ∀ R ∈ degreeHalfRegions116, firstBound 116 R.2 ≤ 22 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Checker. -/

section

namespace UniversalTensorSquare

lemma quickRejected_iff (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) :
    quickRejected fuel n upper A B = true ↔ rejectedRows fuel n upper A B := by
  simp only [quickRejected,rejectedRows,Bool.or_eq_true,Bool.and_eq_true,
    List.any_eq_true,decide_eq_true_eq]
  simp only [or_assoc]

lemma quickAllowed_iff (a : ℕ) (A B : List (ℕ × ℕ)) :
    quickAllowed a A B = true ↔ allowedRow a A B := by
  simp only [quickAllowed,allowedRow,Bool.and_eq_true,List.all_eq_true,
    Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp hk => ?_⟩
    obtain h | h := hB p hp
    · omega
    · exact h
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp => ?_⟩
    by_cases hz : p.1 = 0
    · exact Or.inl hz
    · exact Or.inr (hB p hp (by omega))

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FastRowCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Row Check. -/

section

namespace UniversalTensorSquare

lemma quickBand_sound {M r : ℕ} {rs : List ℕ} (h : quickBand M r rs = true) :
    RowsBand M r rs := by
  obtain ⟨k,hk,hh⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨k,hk,hh.1.1,hh.1.2,hh.2⟩

lemma quickResidual_sound {M r : ℕ} {qs : List (List ℕ)} {t : RowTree} {rs : List ℕ}
    (h : quickResidual M r qs t rs = true) : TreeResidual M r qs t rs := by
  simp only [quickResidual,Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inl (quickBand_sound h))
  · exact Or.inl (Or.inr (Or.inl (quickBand_sound h)))
  · obtain ⟨q,hq,h⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true,decide_eq_true_eq] at h
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,h⟩)))

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_UnionRowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Union Row Checker. -/

section

namespace UniversalTensorSquare

lemma checkRegionPrefixes_sound (P : List ℕ → Bool) (fuel n upper : ℕ)
    (regions : List PrefixRegion) (pref : List ℕ)
    (hc : checkRegionPrefixes P fuel n upper regions pref = true) :
    ∀ A B, (A,B) ∈ regions → ∀ rs ∈ constrainedRows fuel n upper A B,
      P (pref.reverse ++ rs) = true := by
  induction fuel generalizing n upper regions pref with
  | zero =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej hn
    · simp at hrs
    · simp only [List.mem_singleton] at hrs
      subst rs
      have hmem : (A,B) ∈ liveRegions 0 n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions 0 n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      simpa only [checkRegionPrefixes,ite_eq_right hne,ite_eq_left hn,List.append_nil] using hc
    · simp at hrs
  | succ k ih =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej
    · simp at hrs
    · have hmem : (A,B) ∈ liveRegions (k+1) n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions (k+1) n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hrs
      split_ifs at hr with hallowed
      · obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hr
        have hlo : max 1 (n/(k+1)) ≤ a := by
          have hh := Nat.div_le_of_le_mul hallowed.2
          have ha' := (List.mem_range'_1.mp ha).1
          exact max_le ha' hh
        have hai : a ∈ List.range' (max 1 (n/(k+1)))
            (min n upper+1-max 1 (n/(k+1))) := by
          have ha' := List.mem_range'_1.mp ha
          apply List.mem_range'_1.mpr
          refine ⟨hlo, ?_⟩
          have he : max 1 (n/(k+1)) + (min n upper+1-max 1 (n/(k+1))) = min n upper+1 := by
            apply Nat.add_sub_of_le
            omega
          rw [he]
          omega
        rw [checkRegionPrefixes] at hc
        simp only [ite_eq_right hne] at hc
        have hh := List.all_eq_true.mp hc a hai
        rw [ite_eq_left hallowed.2] at hh
        have hnext : (clipBudget A a,rowBudget B a) ∈
            nextRegions a (liveRegions (k+1) n upper regions) := by
          apply List.mem_filterMap.mpr
          refine ⟨(A,B),hmem,?_⟩
          simp only [quickAllowed_iff,ite_eq_left hallowed.1]
        have hi := ih (n-a) a (nextRegions a (liveRegions (k+1) n upper regions))
          (a::pref) hh _ _ hnext ys hy
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hi
      · simp at hr

lemma checkedRegion_diagram {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (μ : YoungDiagram) (hn : μ.card = n) {A B : List (ℕ × ℕ)}
    (hR : (A,B) ∈ regions) (hA : RowBounds μ.transpose A) (hB : RowBounds μ B)
    (hH : firstBound n A ≤ H) (hW : firstBound n B ≤ W) :
    TreeResidual M r qs t μ.rowLens := by
  have hu : ∀ a ∈ μ.rowLens, a ≤ W := by
    intro a ha
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
    rw [← he, YoungDiagram.get_rowLens]
    exact (μ.rowLen_anti _ _ (Nat.zero_le _)).trans ((firstBound_sound μ hn hB).trans hW)
  have hl : μ.rowLens.length ≤ H := by
    rw [YoungDiagram.length_rowLens]
    have hh := (firstBound_sound μ.transpose ((Saxl.transpose_card μ).trans hn) hA).trans hH
    simpa only [YoungDiagram.rowLen_transpose] using hh
  have hmem : μ.rowLens ∈ constrainedRows μ.rowLens.length n W A B := by
    apply mem_constrainedRows _ _ _ _ _ _ rfl
    · exact (Saxl.card_eq_sum_rowLens μ).symm.trans hn
    · exact μ.pos_of_mem_rowLens
    · exact hu
    · exact μ.rowLens_sorted
    · intro p hp
      rw [clippedSum_rowLens]
      exact (hA p hp).2
    · intro p hp
      rw [← rowPrefix_eq_take]
      exact (hB p hp).2
  apply quickResidual_sound
  have hh := checkRegionPrefixes_sound (quickResidual M r qs t) μ.rowLens.length n W
    regions [] (check _ hl) A B hR μ.rowLens hmem
  simpa only [List.reverse_nil,List.nil_append] using hh

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 116. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch116_0 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 0 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_1 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 1 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_2 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 2 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_3 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 3 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_4 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 4 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_5 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 5 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_6 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 6 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_7 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 7 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_8 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 8 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_9 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 9 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_10 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 10 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_11 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 11 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch116_12 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 12 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_13 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 13 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_14 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 14 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_15 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 15 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_16 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 16 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_17 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 17 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_18 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 18 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_19 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 19 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_20 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 20 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_21 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 21 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

lemma degreeUnionBranch116_22 : checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) 22 116 22 degreeHalfRegions116 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SymmetricRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Regions. -/

section

namespace UniversalTensorSquare

lemma treeResidual_transpose {M r : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {μ : YoungDiagram} (h : TreeResidual M r qs t μ.transpose.rowLens) :
    TreeResidual M r qs t μ.rowLens := by
  rcases h with h | h | h
  · rcases h with h | h | ⟨q,hq,h | h⟩ | h | h
    · exact Or.inl (Or.inr (Or.inl (by simpa only [transposeRows_rowLens] using h)))
    · exact Or.inl (Or.inl (by simpa only [transposeRows_rowLens,
        YoungDiagram.transpose_transpose] using h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inr (by
        simpa only [transposeRows_rowLens] using h)⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inl (by
        simpa only [transposeRows_rowLens,YoungDiagram.transpose_transpose] using h)⟩)))
    · simp at h
    · simp at h
  · exact Or.inr (Or.inr (by simpa only [transposeRows_rowLens] using h))
  · exact Or.inr (Or.inl (by simpa only [transposeRows_rowLens,
      YoungDiagram.transpose_transpose] using h))

lemma regionCheck_sound_diagram {n M r d e a b : ℕ} {q : List ℕ}
    {regions : List PrefixRegion} {P : List ℕ → Prop}
    (hc : ∀ R ∈ regions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → P μ.rowLens)
    (h : regionCheck n M r d e a b q regions) :
    semanticResidualCheck n M r d e a b q P := by
  rcases h with h | h | h | ⟨R,hR,hA,hB⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    intro μ hμ ha hb
    exact hc R hR μ hμ (boundsEntail_sound hA _ ha) (boundsEntail_sound hB _ hb)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CheckedUnionSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Union Symmetry. -/

section

namespace UniversalTensorSquare

lemma checkedUnion_symmetric {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions allRegions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (height : ∀ R ∈ regions, firstBound n R.1 ≤ H)
    (width : ∀ R ∈ regions, firstBound n R.2 ≤ W)
    (cover : ∀ R ∈ allRegions, R ∈ regions ∨ (R.2,R.1) ∈ regions) :
    ∀ R ∈ allRegions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → TreeResidual M r qs t μ.rowLens := by
  intro R hR μ hμ hA hB
  rcases cover R hR with h | h
  · exact checkedRegion_diagram check μ hμ h hA hB (height R h) (width R h)
  · apply treeResidual_transpose
    apply checkedRegion_diagram check μ.transpose ((Saxl.transpose_card μ).trans hμ) h
    · simpa only [YoungDiagram.transpose_transpose] using hB
    · exact hA
    · exact height _ h
    · exact width _ h

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 116. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck116 : ∀ h ≤ 22,
    checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) h 116 22 degreeHalfRegions116 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch116_0
  · exact degreeUnionBranch116_1
  · exact degreeUnionBranch116_2
  · exact degreeUnionBranch116_3
  · exact degreeUnionBranch116_4
  · exact degreeUnionBranch116_5
  · exact degreeUnionBranch116_6
  · exact degreeUnionBranch116_7
  · exact degreeUnionBranch116_8
  · exact degreeUnionBranch116_9
  · exact degreeUnionBranch116_10
  · exact degreeUnionBranch116_11
  · exact degreeUnionBranch116_12
  · exact degreeUnionBranch116_13
  · exact degreeUnionBranch116_14
  · exact degreeUnionBranch116_15
  · exact degreeUnionBranch116_16
  · exact degreeUnionBranch116_17
  · exact degreeUnionBranch116_18
  · exact degreeUnionBranch116_19
  · exact degreeUnionBranch116_20
  · exact degreeUnionBranch116_21
  · exact degreeUnionBranch116_22

lemma degreeHalfCover116 : ∀ R ∈ degreeRegions116,
    R ∈ degreeHalfRegions116 ∨ (R.2,R.1) ∈ degreeHalfRegions116 := by decide +kernel

lemma degreeDiagramRegionsChecked116 : ∀ R ∈ degreeRegions116,
    ∀ μ : YoungDiagram, μ.card = 116 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP116 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck116 degreeHalfHeight116 degreeHalfWidth116
    degreeHalfCover116

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck116_oai : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      semanticResidualCheck 116 12 19 (d+1) (e+1) (a+1) (c+1) degreeRows116_0 degreeP116 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked116 (degreeCover116 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeCheck116_oai := @OAI.UniversalTensorSquare.degreeCheck116_oai
