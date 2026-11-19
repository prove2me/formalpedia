-- Prove2me | solution 1 for OAI.UniversalTensorSquare.checkedRegion_diagram
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:37:08.83404+00:00
-- url     : https://prove2.me/submissions/9a93dc94-dcea-45a8-bf9b-792748bb45c1

import Mathlib
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

lemma checkedRegion_diagram_oai {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
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

theorem solution : type_of% @OAI.UniversalTensorSquare.checkedRegion_diagram_oai := @OAI.UniversalTensorSquare.checkedRegion_diagram_oai
