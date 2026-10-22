-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.sl_ordered_basis
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T00:41:16.027797+00:00
-- url     : https://prove2.me/submissions/29346f18-91c6-4113-83f7-79d8caaa55cb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.


namespace SlH
open Matrix

def Sm (t p q : ℕ) : Matrix (Fin t) (Fin t) ℝ :=
  (Matrix.single p q (1 : ℝ)).submatrix (fun i : Fin t => i.val + 1) (fun j : Fin t => j.val + 1)

lemma Sapp (t p q : ℕ) (a b : Fin t) :
    Sm t (p+1) (q+1) a b = if a.val = p ∧ b.val = q then 1 else 0 := by
  simp only [Sm, Matrix.submatrix_apply, Matrix.single_apply]
  congr 1; apply propext; omega

def w (t : ℕ) : (ℕ × ℕ) ⊕ ℕ → Matrix (Fin t) (Fin t) ℝ
  | .inl pq => Sm t (pq.1+1) (pq.2+1)
  | .inr p => Sm t 1 1 - Sm t (p+2) (p+2)

lemma w_inl (t : ℕ) (pq : ℕ × ℕ) (a b : Fin t) :
    w t (.inl pq) a b = if a.val = pq.1 ∧ b.val = pq.2 then 1 else 0 := Sapp t _ _ a b

lemma w_inr (t p : ℕ) (a b : Fin t) :
    w t (.inr p) a b = (if a.val = 0 ∧ b.val = 0 then 1 else 0) -
      (if a.val = p+1 ∧ b.val = p+1 then 1 else 0) := by
  simp only [w, Matrix.sub_apply]
  rw [show (1:ℕ) = 0 + 1 from rfl, Sapp, show p + 2 = (p+1) + 1 from rfl, Sapp]

def L1 (t : ℕ) : List (ℕ × ℕ) :=
  (List.range t).flatMap fun p => ((List.range t).filter fun q => p ≠ q).map fun q => (p, q)

def I (t : ℕ) : List ((ℕ × ℕ) ⊕ ℕ) := (L1 t).map Sum.inl ++ (List.range (t-1)).map Sum.inr

lemma bSl_eq (t : ℕ) : bSl t = (I t).map (w t) := by
  unfold bSl I L1
  rw [List.map_append, List.map_map, List.map_map, List.map_flatMap]
  congr 1
  congr 1; funext p; rw [List.map_map]; rfl

lemma mem_L1 (t : ℕ) (pq : ℕ × ℕ) : pq ∈ L1 t ↔ pq.1 ≠ pq.2 ∧ pq.1 < t ∧ pq.2 < t := by
  obtain ⟨p, q⟩ := pq
  simp only [L1, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hab⟩, rfl, rfl⟩; exact ⟨hab, ha, hb⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨p, h2, q, ⟨h3, h1⟩, rfl, rfl⟩

lemma nodup_L1 (t : ℕ) : (L1 t).Nodup := by
  unfold L1
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

lemma len_L1 (t : ℕ) : (L1 t).length = t*t - t := by
  rw [← List.toFinset_card_of_nodup (nodup_L1 t)]
  have : (L1 t).toFinset = (Finset.range t).offDiag := by
    ext pq; simp only [List.mem_toFinset, mem_L1, Finset.mem_offDiag, Finset.mem_range]; tauto
  rw [this, Finset.offDiag_card, Finset.card_range]

lemma nodup_I (t : ℕ) : (I t).Nodup := by
  unfold I
  rw [List.nodup_append]
  refine ⟨(nodup_L1 t).map Sum.inl_injective, List.nodup_range.map Sum.inr_injective, ?_⟩
  intro x hx y hy hxy
  simp only [List.mem_map] at hx hy
  obtain ⟨a, _, rfl⟩ := hx; obtain ⟨b, _, rfl⟩ := hy; cases hxy

lemma len_I (t : ℕ) (ht : 0 < t) : (I t).length = t^2 - 1 := by
  simp only [I, List.length_append, List.length_map, List.length_range, len_L1]
  have : t*t - t + (t-1) = t^2 - 1 := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t-1, by omega⟩
    simp only [Nat.add_sub_cancel, sq]; ring_nf; omega
  exact this

lemma mem_I_inl (t : ℕ) (pq : ℕ × ℕ) : Sum.inl pq ∈ I t ↔ pq.1 ≠ pq.2 ∧ pq.1 < t ∧ pq.2 < t := by
  simp [I, mem_L1]

lemma mem_I_inr (t : ℕ) (p : ℕ) : Sum.inr p ∈ I t ↔ p + 1 < t := by
  simp [I]; omega

lemma one_sum (t k : ℕ) (hk : k < t) :
    ∑ i : Fin t, (if i.val = k ∧ i.val = k then (1:ℝ) else 0) = 1 := by
  rw [Fintype.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro j hj; rw [if_neg]; intro h; exact hj (Fin.ext h.1)

lemma w_mem (t : ℕ) (ht : 0 < t) (x : (ℕ × ℕ) ⊕ ℕ) (hx : x ∈ I t) :
    w t x ∈ LieAlgebra.SpecialLinear.sl (Fin t) ℝ := by
  show w t x ∈ LinearMap.ker (Matrix.traceLinearMap (Fin t) ℝ ℝ)
  rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace]
  rcases x with ⟨p, q⟩ | p
  · have hm := (mem_I_inl t _).1 hx
    simp only [Matrix.diag_apply, w_inl]
    exact Finset.sum_eq_zero (fun i _ => if_neg (by intro h; exact hm.1 (h.1.symm.trans h.2)))
  · have hm := (mem_I_inr t _).1 hx
    simp only [Matrix.diag_apply, w_inr]
    rw [Finset.sum_sub_distrib, one_sum t 0 ht, one_sum t (p+1) hm, sub_self]

lemma finrank_sl (t : ℕ) (ht : 0 < t) :
    Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin t) ℝ).toSubmodule = t^2 - 1 := by
  have hk : (LieAlgebra.SpecialLinear.sl (Fin t) ℝ).toSubmodule =
      LinearMap.ker (Matrix.traceLinearMap (Fin t) ℝ ℝ) := rfl
  rw [hk]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin t) ℝ ℝ)
  have hr : LinearMap.range (Matrix.traceLinearMap (Fin t) ℝ ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Matrix.single ⟨0, ht⟩ ⟨0, ht⟩ c, by simp [Matrix.traceLinearMap_apply]⟩
  rw [hr, finrank_top, Module.finrank_matrix, Fintype.card_fin] at h
  simp only [Module.finrank_self, mul_one] at h
  rw [sq]; omega

lemma main (t : ℕ) (ht : 0 < t) :
    isBasisFor (LieAlgebra.SpecialLinear.sl (Fin t) ℝ) (listFamily ((I t).map (w t))) := by
  set l := I t with hldef
  have hl : (l.map (w t)).length = l.length := List.length_map _
  let e : Fin (l.map (w t)).length → (ℕ × ℕ) ⊕ ℕ := fun i => l[i.val]'(hl ▸ i.2)
  have he : ∀ i, e i ∈ l := fun i => List.getElem_mem _
  have hv : ∀ i, listFamily (l.map (w t)) i = w t (e i) := by
    intro i; simp [listFamily, e]
  have hinj : ∀ i j, e i = e j → i = j := by
    intro i j h
    exact Fin.ext (((nodup_I t).getElem_inj_iff).1 h)
  clear_value e
  have lin : LinearIndependent ℝ (listFamily (l.map (w t))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rcases hei : e i with ⟨p, q⟩ | p
    · have hm := (mem_I_inl t _).1 (hei ▸ he i)
      have h0 := congrFun (congrFun hg ⟨p, hm.2.1⟩) ⟨q, hm.2.2⟩
      rw [Matrix.sum_apply] at h0
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, hv] at h0
      rw [Finset.sum_eq_single i] at h0
      · rw [hei, w_inl] at h0; simpa using h0
      · intro j _ hji
        rcases hej : e j with ⟨p', q'⟩ | p'
        · rw [w_inl]
          have : ¬ (p = p' ∧ q = q') := by
            rintro ⟨rfl, rfl⟩; exact hji (hinj j i (hej.trans hei.symm))
          simp [this]
        · rw [w_inr]
          have h1 : ¬ (p = 0 ∧ q = 0) := by omega
          have h2 : ¬ (p = p' + 1 ∧ q = p' + 1) := by omega
          simp [h1, h2]
      · intro h; exact absurd (Finset.mem_univ i) h
    · have hm := (mem_I_inr t _).1 (hei ▸ he i)
      have h0 := congrFun (congrFun hg ⟨p+1, hm⟩) ⟨p+1, hm⟩
      rw [Matrix.sum_apply] at h0
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, hv] at h0
      rw [Finset.sum_eq_single i] at h0
      · rw [hei, w_inr] at h0; simpa using h0
      · intro j _ hji
        rcases hej : e j with ⟨p', q'⟩ | p'
        · have hm' := (mem_I_inl t _).1 (hej ▸ he j)
          rw [w_inl]
          have : ¬ (p + 1 = p' ∧ p + 1 = q') := by
            rintro ⟨h1, h2⟩; exact hm'.1 (h1.symm.trans h2)
          simp [this]
        · rw [w_inr]
          have : p' ≠ p := by
            rintro rfl; exact hji (hinj j i (hej.trans hei.symm))
          have h2 : ¬ (p + 1 = p' + 1) := by omega
          simp [h2, Ne.symm this]
      · intro h; exact absurd (Finset.mem_univ i) h
  have hle : Submodule.span ℝ (Set.range (listFamily (l.map (w t)))) ≤
      (LieAlgebra.SpecialLinear.sl (Fin t) ℝ).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hv]; exact w_mem t ht _ (he i)
  refine ⟨lin, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  rw [finrank_span_eq_card lin, Fintype.card_fin, hl, hldef, len_I t ht, finrank_sl t ht]

end SlH

/-- Bsl is an ordered real basis of sl(t), with t^2-1 elements.
Source: PDF pp. 9-10. The positive-size convention includes t=1 and its empty basis. -/
theorem solution (t : ℕ) (ht : 0 < t) :
    (bSl t).length = t ^ 2 - 1 ∧
    isBasisFor (LieAlgebra.SpecialLinear.sl (Fin t) ℝ) (listFamily (bSl t)) := by
  rw [SlH.bSl_eq]
  exact ⟨by rw [List.length_map, SlH.len_I t ht], SlH.main t ht⟩


