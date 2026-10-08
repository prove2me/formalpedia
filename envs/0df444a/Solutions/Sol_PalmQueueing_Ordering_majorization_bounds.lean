-- Prove2me | solution 1 for PalmQueueing.Ordering.majorization_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:24:49.04783+00:00
-- url     : https://prove2.me/submissions/36b0f6ac-2f6c-4bd4-b12e-2b6cc0243202

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders

/-!
# Lemma 4.1.2: the identity and the reversal bracket every reordering (§4.1.3, p.267)
-/


namespace PalmQueueing.Ordering

open Finset

/-- tail sum of a sorted vector as a sum over an index set -/
lemma tail_sum_eq_map {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (l : Fin n) :
    ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), w (σ k)
      = ∑ k ∈ (Ici l).map σ.toEmbedding, w k := by
  rw [Finset.sum_map]
  congr 1
  ext k; simp

lemma card_map_Ici {n : ℕ} (σ : Equiv.Perm (Fin n)) (l : Fin n) :
    ((Ici l).map σ.toEmbedding).card = n - l := by
  rw [Finset.card_map, Fin.card_Ici]

/-- Any subset of cardinality `n - l` has sum at most the tail sum of the sorted vector. -/
lemma sum_le_tail_sum {n : ℕ} (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hσ : Monotone (w ∘ σ)) (l : Fin n) (S : Finset (Fin n)) (hS : S.card = n - l) :
    ∑ k ∈ S, w k ≤ ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), w (σ k) := by
  rw [tail_sum_eq_map]
  set T := (Ici l).map σ.toEmbedding with hT
  have hTcard : T.card = n - l := card_map_Ici σ l
  have hmemT : ∀ a, a ∈ T ↔ l ≤ σ.symm a := by
    intro a
    simp only [hT, Finset.mem_map, Finset.mem_Ici, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨k, hk, rfl⟩; simpa using hk
    · intro h; exact ⟨σ.symm a, h, by simp⟩
  have hc : ∀ a ∈ S \ T, w a ≤ w (σ l) := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    have : ¬ l ≤ σ.symm a := fun h => ha.2 ((hmemT a).2 h)
    have h2 : σ.symm a ≤ l := le_of_lt (not_le.mp this)
    have := hσ h2
    simpa using this
  have hc' : ∀ a ∈ T \ S, w (σ l) ≤ w a := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    have h2 : l ≤ σ.symm a := (hmemT a).1 ha.1
    have := hσ h2
    simpa using this
  have hcard : (S \ T).card = (T \ S).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm, hS, hTcard]
  have h1 : ∑ k ∈ S, w k = ∑ k ∈ S \ T, w k + ∑ k ∈ S ∩ T, w k := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T), Finset.sdiff_union_inter]
  have h2 : ∑ k ∈ T, w k = ∑ k ∈ T \ S, w k + ∑ k ∈ S ∩ T, w k := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter T S),
      Finset.sdiff_union_inter]
  rw [h1, h2]
  have e1 := Finset.sum_le_card_nsmul (S \ T) w (w (σ l)) hc
  have e2 := Finset.card_nsmul_le_sum (T \ S) w (w (σ l)) hc'
  rw [hcard] at e1
  linarith

/-- Subset characterisation of majorization. -/
lemma majorized_iff {n : ℕ} (x y : Fin n → ℝ) :
    Majorized x y ↔
      (∑ k, x k = ∑ k, y k) ∧
      ∀ S : Finset (Fin n), ∃ S' : Finset (Fin n), S'.card = S.card ∧
        ∑ k ∈ S, x k ≤ ∑ k ∈ S', y k := by
  constructor
  · rintro ⟨g, b, hg, hb, hl, htot⟩
    refine ⟨?_, ?_⟩
    · rw [Equiv.sum_comp g x] at htot
      rw [Equiv.sum_comp b y] at htot
      exact htot
    · intro S
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · exact ⟨∅, by simp [h0], by rw [Finset.card_eq_zero.mp h0]; simp⟩
      · have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
        let l : Fin n := ⟨n - S.card, by omega⟩
        have hl' : S.card = n - l := by simp [l]; omega
        refine ⟨(Ici l).map b.toEmbedding, ?_, ?_⟩
        · rw [card_map_Ici]; exact hl'.symm
        · calc ∑ k ∈ S, x k ≤ ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), x (g k) :=
                sum_le_tail_sum x g hg l S hl'
            _ ≤ ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), y (b k) := hl l
            _ = _ := tail_sum_eq_map y b l
  · rintro ⟨htot, hS⟩
    refine ⟨Tuple.sort x, Tuple.sort y, Tuple.monotone_sort x, Tuple.monotone_sort y, ?_, ?_⟩
    · intro l
      rw [tail_sum_eq_map x]
      obtain ⟨S', hS'c, hS'⟩ := hS ((Ici l).map (Tuple.sort x).toEmbedding)
      rw [card_map_Ici] at hS'c
      exact hS'.trans (sum_le_tail_sum y _ (Tuple.monotone_sort y) l S' hS'c)
    · rw [Equiv.sum_comp, Equiv.sum_comp]; exact htot

lemma majorized_refl {n : ℕ} (x : Fin n → ℝ) : Majorized x x :=
  (majorized_iff x x).2 ⟨rfl, fun S => ⟨S, rfl, le_rfl⟩⟩

lemma majorized_trans {n : ℕ} {x y z : Fin n → ℝ} (h1 : Majorized x y) (h2 : Majorized y z) :
    Majorized x z := by
  rw [majorized_iff] at *
  refine ⟨h1.1.trans h2.1, fun S => ?_⟩
  obtain ⟨S', h1c, h1s⟩ := h1.2 S
  obtain ⟨S'', h2c, h2s⟩ := h2.2 S'
  exact ⟨S'', h2c.trans h1c, h1s.trans h2s⟩

theorem majorization_interchange_core {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y)
    (g : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i < j) (hgij : g j < g i)
    (g' : Equiv.Perm (Fin n))
    (hg'i : g' i = g j) (hg'j : g' j = g i)
    (hg'k : ∀ k : Fin n, k ≠ i → k ≠ j → g' k = g k) :
    Majorized (fun k => y (g' k) - x k) (fun k => y (g k) - x k) := by
  classical
  set u : Fin n → ℝ := fun k => y (g k) - x k with hu
  set v : Fin n → ℝ := fun k => y (g' k) - x k with hv
  set d : ℝ := y (g j) - y (g i) with hd
  have hd0 : d ≤ 0 := by
    have := hy hgij.le; simp [hd]; linarith
  have hxij : x i ≤ x j := hx hij.le
  have hne : i ≠ j := ne_of_lt hij
  have hpt : ∀ k, v k = u k + ((if k = i then d else 0) + (if k = j then -d else 0)) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [hu, hv, hd, hg'i, hne]
    · by_cases hkj : k = j
      · subst hkj; simp [hu, hv, hd, hg'j, Ne.symm hne]
      · simp [hu, hv, hki, hkj, hg'k k hki hkj]
  have hsum : ∀ S : Finset (Fin n), ∑ k ∈ S, v k =
      ∑ k ∈ S, u k + ((if i ∈ S then d else 0) + (if j ∈ S then -d else 0)) := by
    intro S
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  rw [majorized_iff]
  refine ⟨?_, ?_⟩
  · show ∑ k, v k = ∑ k, u k
    rw [hsum]; simp
  · intro S
    by_cases hiS : i ∈ S
    · refine ⟨S, rfl, ?_⟩
      rw [hsum]
      by_cases hjS : j ∈ S
      · simp [hiS, hjS]
      · simp [hiS, hjS]; linarith
    · by_cases hjS : j ∈ S
      · refine ⟨insert i (S.erase j), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hjS]
          · have : 1 ≤ S.card := Finset.card_pos.mpr ⟨j, hjS⟩
            omega
          · simp [hiS]
        · rw [hsum, Finset.sum_insert, Finset.sum_erase_eq_sub hjS]
          · simp only [hiS, hjS, if_false, if_true, zero_add]
            show ∑ k ∈ S, u k + -d ≤ u i + (∑ k ∈ S, u k - u j)
            simp only [hu, hd]
            linarith
          · simp [hiS]
      · refine ⟨S, rfl, ?_⟩
        rw [hsum]; simp [hiS, hjS]


/-- Lower bound: the identity pairing is majorized by any reordering. -/
lemma majorized_id_le {n : ℕ} (x y : Fin n → ℝ) (hx : Monotone x) (hy : Monotone y) :
    ∀ g : Equiv.Perm (Fin n), Majorized (fun k => y k - x k) (fun k => y (g k) - x k) := by
  classical
  intro g
  induction' hm : (univ.filter (fun k : Fin n => g k ≠ k)).card using Nat.strong_induction_on
    with m ih generalizing g
  by_cases hm0 : m = 0
  · subst hm0
    have hfix : ∀ k, g k = k := by
      intro k
      by_contra hk
      have : k ∈ univ.filter (fun k : Fin n => g k ≠ k) := by simp [hk]
      rw [Finset.card_eq_zero.mp hm] at this
      simp at this
    simp only [hfix]
    exact majorized_refl _
  · set NF := univ.filter (fun k : Fin n => g k ≠ k) with hNF
    have hne : NF.Nonempty := by
      rw [← Finset.card_pos, hm]; omega
    set i := NF.min' hne with hi
    have hiNF : i ∈ NF := Finset.min'_mem _ _
    have hgi : g i ≠ i := by simpa [hNF] using hiNF
    have hmin : ∀ k, k < i → g k = k := by
      intro k hk
      by_contra h
      have : k ∈ NF := by simp [hNF, h]
      have := Finset.min'_le NF k this
      rw [← hi] at this
      exact absurd hk (not_lt.mpr this)
    have hgi' : i < g i := by
      rcases lt_trichotomy (g i) i with h | h | h
      · have := hmin (g i) h
        exact absurd (g.injective this) hgi
      · exact absurd h hgi
      · exact h
    set j := g.symm i with hj
    have hgj : g j = i := by simp [hj]
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · exact absurd (by rw [← h] at hgj; exact hgj) hgi
      · have := hmin j h; rw [hgj] at this; exact absurd this (ne_of_lt h).symm
    have hgij : g j < g i := by rw [hgj]; exact hgi'
    set g' : Equiv.Perm (Fin n) := g * Equiv.swap i j with hg'
    have hg'i : g' i = g j := by simp [hg']
    have hg'j : g' j = g i := by simp [hg']
    have hg'k : ∀ k : Fin n, k ≠ i → k ≠ j → g' k = g k := by
      intro k hki hkj; simp [hg', Equiv.swap_apply_of_ne_of_ne hki hkj]
    have hstep := majorization_interchange_core x y hx hy g i j hij hgij g' hg'i hg'j hg'k
    have hsub : univ.filter (fun k : Fin n => g' k ≠ k) ⊂ NF := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, hiNF, ?_⟩
        simp [hg'i, hgj]
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [hNF, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hki : k = i
        · subst hki; rw [hg'i, hgj] at hk; exact absurd rfl hk
        · by_cases hkj : k = j
          · subst hkj; rw [hgj]; exact (ne_of_lt hij)
          · rwa [hg'k k hki hkj] at hk
    have hlt := Finset.card_lt_card hsub
    rw [hm] at hlt
    exact majorized_trans (ih _ hlt g' rfl) hstep

/-- Upper bound: any reordering is majorized by the reversal pairing. -/
lemma majorized_le_rev {n : ℕ} (x y : Fin n → ℝ) (hx : Monotone x) (hy : Monotone y) :
    ∀ g : Equiv.Perm (Fin n),
      Majorized (fun k => y (g k) - x k) (fun k => y (Fin.revPerm k) - x k) := by
  classical
  intro g
  induction' hm : (univ.filter (fun k : Fin n => g k ≠ Fin.revPerm k)).card
    using Nat.strong_induction_on with m ih generalizing g
  by_cases hm0 : m = 0
  · subst hm0
    have hfix : ∀ k, g k = Fin.revPerm k := by
      intro k
      by_contra hk
      have : k ∈ univ.filter (fun k : Fin n => g k ≠ Fin.revPerm k) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk
      rw [Finset.card_eq_zero.mp hm] at this
      simp at this
    simp only [hfix]
    exact majorized_refl _
  · set NF := univ.filter (fun k : Fin n => g k ≠ Fin.revPerm k) with hNF
    have hne : NF.Nonempty := by
      rw [← Finset.card_pos, hm]; omega
    set i := NF.min' hne with hi
    have hiNF : i ∈ NF := Finset.min'_mem _ _
    have hgi : g i ≠ Fin.rev i := by simpa [hNF] using hiNF
    have hmin : ∀ k, k < i → g k = Fin.rev k := by
      intro k hk
      by_contra h
      have : k ∈ NF := by simp [hNF, h]
      have := Finset.min'_le NF k this
      rw [← hi] at this
      exact absurd hk (not_lt.mpr this)
    have hgi' : g i < Fin.rev i := by
      rcases lt_trichotomy (g i) (Fin.rev i) with h | h | h
      · exact h
      · exact absurd h hgi
      · -- rev i < g i, so rev (g i) < i
        have h2 : Fin.rev (g i) < i := by
          have := Fin.rev_lt_rev.mpr h
          simpa using this
        have := hmin _ h2
        rw [Fin.rev_rev] at this
        exact absurd (g.injective this) (ne_of_lt h2)
    set j := g.symm (Fin.rev i) with hj
    have hgj : g j = Fin.rev i := by simp [hj]
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · exact absurd (by rw [← h] at hgj; exact hgj) hgi
      · have := hmin j h; rw [hgj] at this
        exact absurd (Fin.rev_injective this).symm (ne_of_lt h)
    have hgij : g i < g j := by rw [hgj]; exact hgi'
    set g₁ : Equiv.Perm (Fin n) := g * Equiv.swap i j with hg₁
    have hg₁i : g₁ i = g j := by simp [hg₁]
    have hg₁j : g₁ j = g i := by simp [hg₁]
    have hg₁k : ∀ k : Fin n, k ≠ i → k ≠ j → g k = g₁ k := by
      intro k hki hkj; simp [hg₁, Equiv.swap_apply_of_ne_of_ne hki hkj]
    have hstep := majorization_interchange_core x y hx hy g₁ i j hij
      (by rw [hg₁i, hg₁j]; exact hgij) g hg₁j.symm hg₁i.symm hg₁k
    have hsub : univ.filter (fun k : Fin n => g₁ k ≠ Fin.revPerm k) ⊂ NF := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, hiNF, ?_⟩
        simp [hg₁i, hgj]
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp only [hNF, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hki : k = i
        · subst hki; rw [hg₁i, hgj] at hk; exact absurd (by simp) hk
        · by_cases hkj : k = j
          · subst hkj; rw [hgj]
            intro h
            exact (ne_of_lt hij) (Fin.rev_injective (by simpa using h))
          · rwa [← hg₁k k hki hkj] at hk
    have hlt := Finset.card_lt_card hsub
    rw [hm] at hlt
    exact majorized_trans hstep (ih _ hlt g₁ rfl)

theorem majorization_bounds_core {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y) (g : Equiv.Perm (Fin n)) :
    Majorized (fun k => y k - x k) (fun k => y (g k) - x k) ∧
    Majorized (fun k => y (g k) - x k) (fun k => reverseVec y k - x k) := by
  refine ⟨majorized_id_le x y hx hy g, ?_⟩
  have := majorized_le_rev x y hx hy g
  simpa [reverseVec] using this

end PalmQueueing.Ordering

open PalmQueueing.Ordering


theorem solution {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y) (g : Equiv.Perm (Fin n)) :
    Majorized (fun k => y k - x k) (fun k => y (g k) - x k) ∧
    Majorized (fun k => y (g k) - x k) (fun k => reverseVec y k - x k) := by
  exact majorization_bounds_core x y hx hy g
