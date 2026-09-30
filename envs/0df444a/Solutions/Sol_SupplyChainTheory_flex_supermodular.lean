-- Prove2me | solution 1 for SupplyChainTheory.flex_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T07:01:50.584209+00:00
-- url     : https://prove2.me/submissions/453c6151-1194-475f-8df6-4dc48b9c7d46

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

set_option autoImplicit false

open SupplyChainTheory in
lemma fs_lc_off {n : ℕ} {i j : Fin n} (h : (i, j) ∈ longChain n) (hne : i ≠ j) :
    i = finRotate n j := by
  unfold longChain dedicated at h
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.mk.injEq] at h
  rcases h with ⟨k, hk1, hk2⟩ | ⟨k, hk1, hk2⟩
  · exact absurd (hk1.symm.trans hk2) hne
  · subst hk2; exact hk1.symm

open SupplyChainTheory in
lemma fs_bdd {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι)) :
    BddAbove {v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} := by
  refine ⟨∑ i, d i, ?_⟩
  rintro v ⟨y, hy, rfl⟩
  exact Finset.sum_le_sum fun i _ => hy.2.2.2 i

open SupplyChainTheory in
lemma fs_nonempty {ι : Type*} [Fintype ι] (C : ℝ) (hC : 0 ≤ C) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) (E : Finset (ι × ι)) :
    ({v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} : Set ℝ).Nonempty :=
  ⟨0, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ => by simp [hC],
    fun i => by simp [hd i]⟩, by simp⟩

open SupplyChainTheory in
lemma fs_le_perf {ι : Type*} [Fintype ι] (C : ℝ) (d : ι → ℝ) (E : Finset (ι × ι))
    (y : ι → ι → ℝ) (hy : FlexFeasible C d E y) : ∑ i, ∑ j, y i j ≤ perf C d E :=
  le_csSup (fs_bdd C d E) ⟨y, hy, rfl⟩

open SupplyChainTheory in
lemma fs_sum_le {n : ℕ} (f y1 y2 : Fin n → ℝ) (B : ℝ) (h1 : ∑ i, y1 i ≤ B)
    (h2 : ∑ i, y2 i ≤ B) (hf : (∀ i, f i ≤ y1 i) ∨ (∀ i, f i ≤ y2 i)) : ∑ i, f i ≤ B := by
  rcases hf with hf | hf
  · exact (Finset.sum_le_sum fun i _ => hf i).trans h1
  · exact (Finset.sum_le_sum fun i _ => hf i).trans h2

open SupplyChainTheory in
lemma fs_key {n : ℕ} (C : ℝ) (d : Fin n → ℝ) (E : Finset (Fin n × Fin n))
    (hE : E ⊆ longChain n) (a b : Fin n × Fin n) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b)
    (y1 y2 : Fin n → Fin n → ℝ) (h1 : FlexFeasible C d (E \ {a}) y1)
    (h2 : FlexFeasible C d (E \ {b}) y2) :
    ∑ i, ∑ j, y1 i j + ∑ i, ∑ j, y2 i j ≤ perf C d E + perf C d (E \ {a, b}) := by
  -- zeros off E and off the long chain
  have z1E : ∀ i j, (i, j) ∉ E → y1 i j = 0 := fun i j hn =>
    h1.2.1 i j (fun hm => hn (Finset.mem_sdiff.1 hm).1)
  have z2E : ∀ i j, (i, j) ∉ E → y2 i j = 0 := fun i j hn =>
    h2.2.1 i j (fun hm => hn (Finset.mem_sdiff.1 hm).1)
  have z1 : ∀ i j, i ≠ j → i ≠ finRotate n j → y1 i j = 0 := fun i j hne hr =>
    z1E i j (fun hm => hr (fs_lc_off (hE hm) hne))
  have z2 : ∀ i j, i ≠ j → i ≠ finRotate n j → y2 i j = 0 := fun i j hne hr =>
    z2E i j (fun hm => hr (fs_lc_off (hE hm) hne))
  have y1a : y1 a.1 a.2 = 0 := h1.2.1 _ _ (by simp)
  have y2b : y2 b.1 b.2 = 0 := h2.2.1 _ _ (by simp)
  let g : Fin n → Fin n → ℝ := fun i j =>
    if i = j then min (y1 i j) (y2 i j) else max (y1 i j) (y2 i j)
  let h : Fin n → Fin n → ℝ := fun i j =>
    if i = j then max (y1 i j) (y2 i j) else min (y1 i j) (y2 i j)
  have hsum : ∑ i, ∑ j, y1 i j + ∑ i, ∑ j, y2 i j = ∑ i, ∑ j, g i j + ∑ i, ∑ j, h i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, h]
    split_ifs
    · linarith [min_add_max (y1 i j) (y2 i j)]
    · linarith [min_add_max (y1 i j) (y2 i j)]
  have hg : FlexFeasible C d E g := by
    refine ⟨fun i j => ?_, fun i j hn => ?_, fun j => ?_, fun i => ?_⟩
    · simp only [g]
      split_ifs
      · exact le_min (h1.1 i j) (h2.1 i j)
      · exact le_max_of_le_left (h1.1 i j)
    · simp [g, z1E i j hn, z2E i j hn]
    · refine fs_sum_le (fun i => g i j) (fun i => y1 i j) (fun i => y2 i j) C
        (h1.2.2.1 j) (h2.2.2.1 j) ?_
      rcases le_total (y1 (finRotate n j) j) (y2 (finRotate n j) j) with hle | hle
      · right
        intro i
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_right _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · subst hr; rw [max_eq_right hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
      · left
        intro i
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_left _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · subst hr; rw [max_eq_left hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
    · refine fs_sum_le (fun j => g i j) (fun j => y1 i j) (fun j => y2 i j) (d i)
        (h1.2.2.2 i) (h2.2.2.2 i) ?_
      set j0 := (finRotate n).symm i with hj0
      have hi0 : i = finRotate n j0 := by rw [hj0, Equiv.apply_symm_apply]
      rcases le_total (y1 i j0) (y2 i j0) with hle | hle
      · right
        intro j
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_right _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · have : j = j0 := by
              rw [hi0] at hr; exact ((finRotate n).injective hr).symm
            subst this; rw [max_eq_right hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
      · left
        intro j
        simp only [g]
        by_cases hij : i = j
        · rw [if_pos hij]; exact min_le_left _ _
        · rw [if_neg hij]
          by_cases hr : i = finRotate n j
          · have : j = j0 := by
              rw [hi0] at hr; exact ((finRotate n).injective hr).symm
            subst this; rw [max_eq_left hle]
          · rw [z1 i j hij hr, z2 i j hij hr, max_self]
  have hh : FlexFeasible C d (E \ {a, b}) h := by
    refine ⟨fun i j => ?_, fun i j hn => ?_, fun j => ?_, fun i => ?_⟩
    · simp only [h]
      split_ifs
      · exact le_max_of_le_left (h1.1 i j)
      · exact le_min (h1.1 i j) (h2.1 i j)
    · by_cases hm : (i, j) ∈ E
      · have hab : (i, j) = a ∨ (i, j) = b := by
          by_contra hc
          push Not at hc
          exact hn (by simp [hm, hc.1, hc.2])
        rcases hab with hab | hab
        · have hne : i ≠ j := by
            intro he; apply hfa; rw [← hab]; exact he
          simp only [h, if_neg hne]
          have : y1 i j = 0 := by rw [← y1a, ← hab]
          rw [this]; exact min_eq_left (h2.1 i j)
        · have hne : i ≠ j := by
            intro he; apply hfb; rw [← hab]; exact he
          simp only [h, if_neg hne]
          have : y2 i j = 0 := by rw [← y2b, ← hab]
          rw [this]; exact min_eq_right (h1.1 i j)
      · simp [h, z1E i j hm, z2E i j hm]
    · refine fs_sum_le (fun i => h i j) (fun i => y1 i j) (fun i => y2 i j) C
        (h1.2.2.1 j) (h2.2.2.1 j) ?_
      rcases le_total (y1 j j) (y2 j j) with hle | hle
      · right
        intro i
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_right hle]
        · rw [if_neg hij]; exact min_le_right _ _
      · left
        intro i
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_left hle]
        · rw [if_neg hij]; exact min_le_left _ _
    · refine fs_sum_le (fun j => h i j) (fun j => y1 i j) (fun j => y2 i j) (d i)
        (h1.2.2.2 i) (h2.2.2.2 i) ?_
      rcases le_total (y1 i i) (y2 i i) with hle | hle
      · right
        intro j
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_right hle]
        · rw [if_neg hij]; exact min_le_right _ _
      · left
        intro j
        simp only [h]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, max_eq_left hle]
        · rw [if_neg hij]; exact min_le_left _ _
  rw [hsum]
  exact add_le_add (fs_le_perf C d E g hg) (fs_le_perf C d _ h hh)

open SupplyChainTheory in
theorem solution {n : ℕ} (C : ℝ) (hC : 0 ≤ C) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ longChain n) (a b : Fin n × Fin n)
    (ha : a ∈ E) (hb : b ∈ E) (hfa : IsFlexEdge a) (hfb : IsFlexEdge b) :
    perf C d (E \ {a}) + perf C d (E \ {b}) ≤ perf C d E + perf C d (E \ {a, b}) := by
  have key := fs_key C d E hE a b hfa hfb
  unfold perf
  set X := sSup {v | ∃ y, FlexFeasible C d E y ∧ v = ∑ i, ∑ j, y i j} +
    sSup {v | ∃ y, FlexFeasible C d (E \ {a, b}) y ∧ v = ∑ i, ∑ j, y i j} with hX
  have step : ∀ y1, FlexFeasible C d (E \ {a}) y1 →
      sSup {v | ∃ y, FlexFeasible C d (E \ {b}) y ∧ v = ∑ i, ∑ j, y i j}
        ≤ X - ∑ i, ∑ j, y1 i j := by
    intro y1 h1
    refine csSup_le (fs_nonempty C hC d hd _) ?_
    rintro v ⟨y2, h2, rfl⟩
    have := key y1 y2 h1 h2
    unfold perf at this
    linarith
  have : sSup {v | ∃ y, FlexFeasible C d (E \ {a}) y ∧ v = ∑ i, ∑ j, y i j}
      ≤ X - sSup {v | ∃ y, FlexFeasible C d (E \ {b}) y ∧ v = ∑ i, ∑ j, y i j} := by
    refine csSup_le (fs_nonempty C hC d hd _) ?_
    rintro v ⟨y1, h1, rfl⟩
    have := step y1 h1
    linarith
  linarith

