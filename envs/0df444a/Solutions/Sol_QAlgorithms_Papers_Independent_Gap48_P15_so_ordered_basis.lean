-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.so_ordered_basis
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T00:38:54.790884+00:00
-- url     : https://prove2.me/submissions/4e3ee528-4156-4a8e-ad01-acec840e7866

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.


namespace SoH
open Matrix

def L (t : ℕ) : List (ℕ × ℕ) :=
  (List.range t).flatMap fun p => ((List.range t).filter fun q => p < q).map fun q => (p, q)

lemma mem_L (t : ℕ) (pq : ℕ × ℕ) : pq ∈ L t ↔ pq.1 < pq.2 ∧ pq.2 < t := by
  obtain ⟨p, q⟩ := pq
  simp only [L, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hab⟩, rfl, rfl⟩; exact ⟨hab, hb⟩
  · rintro ⟨h1, h2⟩; exact ⟨p, by omega, q, ⟨h2, h1⟩, rfl, rfl⟩

lemma nodup_L (t : ℕ) : (L t).Nodup := by
  unfold L
  rw [List.nodup_flatMap]
  constructor
  · intro p _
    exact List.Nodup.map (fun a b h => by simpa using h) (List.nodup_range.filter _)
  · refine List.Pairwise.imp ?_ List.nodup_range
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx1 hx2
    simp only [List.mem_map, List.mem_filter] at hx1 hx2
    obtain ⟨q1, _, rfl⟩ := hx1
    obtain ⟨q2, _, h⟩ := hx2
    simp only [Prod.mk.injEq] at h
    exact hab h.1.symm

lemma bSo_eq (t : ℕ) : bSo t = (L t).map (fun pq => QAlgorithms.Papers.Independent.Gap48.P15.J t (pq.1+1) (pq.2+1)) := by
  unfold bSo L
  rw [List.map_flatMap]
  congr 1; funext p; rw [List.map_map]; rfl

lemma Japply (t p q : ℕ) (i j : Fin t) : QAlgorithms.Papers.Independent.Gap48.P15.J t (p+1) (q+1) i j =
    (if i.val = p ∧ j.val = q then 1 else 0) - (if i.val = q ∧ j.val = p then 1 else 0) := by
  simp only [QAlgorithms.Papers.Independent.Gap48.P15.J, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.single_apply]
  congr 1
  · congr 1; apply propext; omega
  · congr 1; apply propext; omega

lemma card_pairs (t : ℕ) :
    ((Finset.range t ×ˢ Finset.range t).filter (fun pq : ℕ × ℕ => pq.1 < pq.2)).card = t*(t-1)/2 := by
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  have : ∀ q ∈ Finset.range t, (∑ p ∈ Finset.range t, if p < q then 1 else 0) = q := by
    intro q hq
    rw [← Finset.card_filter]
    have : (Finset.range t).filter (fun p => p < q) = Finset.range q := by
      ext p; simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢; omega
    rw [this, Finset.card_range]
  rw [Finset.sum_congr rfl this, Finset.sum_range_id]

lemma len_L (t : ℕ) : (L t).length = t*(t-1)/2 := by
  rw [← List.toFinset_card_of_nodup (nodup_L t), ← card_pairs]
  congr 1; ext pq
  simp only [List.mem_toFinset, mem_L, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

lemma main (t : ℕ) (l : List (ℕ × ℕ)) (hn : l.Nodup)
    (hm : ∀ pq, pq ∈ l ↔ pq.1 < pq.2 ∧ pq.2 < t) :
    isBasisFor (LieAlgebra.Orthogonal.so (Fin t) ℝ)
      (listFamily (l.map (fun pq => QAlgorithms.Papers.Independent.Gap48.P15.J t (pq.1+1) (pq.2+1)))) := by
  set w : ℕ × ℕ → Matrix (Fin t) (Fin t) ℝ := fun pq => QAlgorithms.Papers.Independent.Gap48.P15.J t (pq.1+1) (pq.2+1) with hw
  have hl : (l.map w).length = l.length := List.length_map _
  let e : Fin (l.map w).length → ℕ × ℕ := fun i => l[i.val]'(hl ▸ i.2)
  have he : ∀ i, e i ∈ l := fun i => List.getElem_mem _
  have hv : ∀ i, listFamily (l.map w) i = w (e i) := by
    intro i; simp [listFamily, e]
  have hinj : ∀ i j, e i = e j → i = j := by
    intro i j h
    exact Fin.ext ((hn.getElem_inj_iff).1 h)
  have hget : ∀ i : Fin (l.map w).length, ∀ n (hn' : n < l.length), i.val = n → e i = l[n] := by
    intro i n hn' h; simp only [e, h]
  clear_value e
  have hvap : ∀ i (a b : Fin t), listFamily (l.map w) i a b =
      (if a.val = (e i).1 ∧ b.val = (e i).2 then 1 else 0) -
      (if a.val = (e i).2 ∧ b.val = (e i).1 then 1 else 0) := by
    intro i a b; rw [hv]; exact Japply _ _ _ a b
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hpq := (hm _).1 (he i)
    have h0 := congrFun (congrFun hg ⟨(e i).1, by omega⟩) ⟨(e i).2, hpq.2⟩
    rw [Matrix.sum_apply] at h0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, hvap] at h0
    have hne : ¬((e i).1 = (e i).2 ∧ (e i).2 = (e i).1) := by omega
    rw [Finset.sum_eq_single i] at h0
    · simpa [hne] using h0
    · intro j _ hji
      have hj := (hm _).1 (he j)
      have h1 : ¬ ((e i).1 = (e j).1 ∧ (e i).2 = (e j).2) := by
        intro h; exact hji (hinj j i (Prod.ext h.1.symm h.2.symm))
      have h2 : ¬ ((e i).1 = (e j).2 ∧ (e i).2 = (e j).1) := by omega
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show listFamily (l.map w) i ∈ LieAlgebra.Orthogonal.so (Fin t) ℝ
    rw [LieAlgebra.Orthogonal.mem_so]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, hvap]
    have hj := (hm _).1 (he i)
    split_ifs <;> first | (exfalso; omega) | ring
  · intro A hA
    have hA2 : A ∈ LieAlgebra.Orthogonal.so (Fin t) ℝ := hA
    rw [LieAlgebra.Orthogonal.mem_so] at hA2
    have hA' : Aᵀ = -A := hA2
    have hsk : ∀ a b, A b a = -A a b := fun a b => by
      have := congrFun (congrFun hA' a) b; simpa using this
    let c : ℕ → ℕ → ℝ := fun p q => if h : p < t ∧ q < t then A ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
    have hc : ∀ a b : Fin t, c a.val b.val = A a b := fun a b => by simp [c]
    have hdec : A = ∑ i, c (e i).1 (e i).2 • listFamily (l.map w) i := by
      ext a b
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, hvap]
      rcases lt_trichotomy a.val b.val with hab | hab | hab
      · obtain ⟨n, hn', hget'⟩ := List.mem_iff_getElem.1 ((hm (a.val, b.val)).2 ⟨hab, b.2⟩)
        let i0 : Fin (l.map w).length := ⟨n, hl ▸ hn'⟩
        have hi0 : e i0 = (a.val, b.val) := by rw [hget i0 n hn' rfl]; exact hget'
        rw [Finset.sum_eq_single i0]
        · rw [hi0]; simp [hc, show ¬(a.val = b.val ∧ b.val = a.val) by omega]
        · intro j _ hj
          have hjm := (hm _).1 (he j)
          have h1 : ¬ (a.val = (e j).1 ∧ b.val = (e j).2) := by
            intro h; apply hj; apply hinj; rw [hi0]; exact Prod.ext h.1.symm h.2.symm
          have h2 : ¬ (a.val = (e j).2 ∧ b.val = (e j).1) := by omega
          simp [h1, h2]
        · intro h; exact absurd (Finset.mem_univ i0) h
      · have : a = b := Fin.ext hab
        subst this
        have h0 : A a a = 0 := by have := hsk a a; linarith
        rw [h0]; symm; apply Finset.sum_eq_zero; intro j _
        have hjm := (hm _).1 (he j)
        have h1 : ¬ (a.val = (e j).1 ∧ a.val = (e j).2) := by omega
        have h2 : ¬ (a.val = (e j).2 ∧ a.val = (e j).1) := by omega
        simp [h1, h2]
      · obtain ⟨n, hn', hget'⟩ := List.mem_iff_getElem.1 ((hm (b.val, a.val)).2 ⟨hab, a.2⟩)
        let i0 : Fin (l.map w).length := ⟨n, hl ▸ hn'⟩
        have hi0 : e i0 = (b.val, a.val) := by rw [hget i0 n hn' rfl]; exact hget'
        rw [Finset.sum_eq_single i0]
        · rw [hi0]
          have hne : ¬(a.val = b.val ∧ b.val = a.val) := by omega
          simp [hc, hne, hsk a b]
        · intro j _ hj
          have hjm := (hm _).1 (he j)
          have h2 : ¬ (a.val = (e j).2 ∧ b.val = (e j).1) := by
            intro h; apply hj; apply hinj; rw [hi0]; exact Prod.ext h.2.symm h.1.symm
          have h1 : ¬ (a.val = (e j).1 ∧ b.val = (e j).2) := by omega
          simp [h1, h2]
        · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hdec]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

end SoH

/-- BSo is an ordered real basis of so(t), including its stated cardinality.
Source: PDF p. 5, BSo. The positive-size convention includes t=1 and its empty basis. -/
theorem solution (t : ℕ) (ht : 0 < t) :
    (bSo t).length = t * (t - 1) / 2 ∧
    isBasisFor (LieAlgebra.Orthogonal.so (Fin t) ℝ) (listFamily (bSo t)) := by
  rw [SoH.bSo_eq]
  exact ⟨by rw [List.length_map, SoH.len_L], SoH.main t _ (SoH.nodup_L t) (SoH.mem_L t)⟩



