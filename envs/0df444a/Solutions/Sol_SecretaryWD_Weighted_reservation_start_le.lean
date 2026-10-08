-- Prove2me | solution 1 for SecretaryWD.Weighted.reservation_start_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:28:15.935985+00:00
-- url     : https://prove2.me/submissions/20bbeeeb-3e58-466e-aa13-c91f22f78735

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm



namespace SecretaryWD.Weighted

open Classical

lemma rs_better_irrefl {n : ℕ} (v : Fin n → ℝ) (e : Fin n) : ¬ better v e e := by
  unfold better; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma rs_better_trans {n : ℕ} (v : Fin n → ℝ) (a b c : Fin n) :
    better v a b → better v b c → better v a c := by
  unfold better
  rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma rs_better_total {n : ℕ} (v : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    better v a b ∨ better v b a := by
  unfold better
  rcases lt_trichotomy (v a) (v b) with h | h | h
  · right; left; exact h
  · rcases lt_trichotomy a.val b.val with h' | h' | h'
    · left; right; exact ⟨h, h'⟩
    · exact absurd (Fin.ext h') hab
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

lemma rs_rank_injOn {n : ℕ} (v : Fin n → ℝ) (T : Finset (Fin n)) :
    Set.InjOn (fun e => (T.filter (fun f => better v f e)).card) (T : Set (Fin n)) := by
  intro a ha b hb hab
  by_contra hne
  have key : ∀ x y : Fin n, x ∈ T → better v x y →
      (T.filter (fun f => better v f x)).card < (T.filter (fun f => better v f y)).card := by
    intro x y hx hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨x, by simp [hx, hxy], by simp [rs_better_irrefl]⟩
    · intro f hf
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, rs_better_trans v _ _ _ hf.2 hxy⟩
  rcases rs_better_total v a b hne with h | h
  · have := key a b ha h; simp only at hab; omega
  · have := key b a hb h; simp only at hab; omega

lemma rs_top_card_le {n : ℕ} (v : Fin n → ℝ) (T : Finset (Fin n)) (K : ℕ) :
    (T.filter (fun e => (T.filter (fun f => better v f e)).card < K)).card ≤ K := by
  have h := Finset.card_le_card_of_injOn
    (fun e => (T.filter (fun f => better v f e)).card)
    (s := T.filter (fun e => (T.filter (fun f => better v f e)).card < K))
    (t := Finset.range K)
    (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; simpa using he.2)
    ((rs_rank_injOn v T).mono (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1))
  simpa using h

lemma rs_class_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : valueClass x ≤ valueClass y := by
  unfold valueClass
  rw [if_pos hx, if_pos (lt_of_lt_of_le hx hxy)]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.log_le_log hx hxy
  have : Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := div_le_div_of_nonneg_right this h2.le
  have := Int.floor_mono this
  omega

theorem rs_core {n K : ℕ} (v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) :
    reservationStart v π τ K i ≤ optimalStart (K := K) v i := by
  set C : Finset (Fin n) := Finset.univ.filter (fun e => 0 < v e ∧ i < valueClass (v e)) with hC
  have hup : ∀ e f, e ∈ C → better v f e → f ∈ C := by
    intro e f he hfe
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have hle : v e ≤ v f := by
      rcases hfe with h | ⟨h, _⟩
      · exact h.le
      · exact h.ge
    exact ⟨lt_of_lt_of_le he.1 hle, lt_of_lt_of_le he.2 (rs_class_mono he.1 hle)⟩
  -- rank equals rank within C
  have hrank : ∀ e ∈ C, valueRank v e = (C.filter (fun f => better v f e)).card := by
    intro e he
    unfold valueRank
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨hup e f he h, h⟩
    · intro h; exact h.2
  have hB : optimalStart (K := K) v i = (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).card := by
    unfold optimalStart
    congr 1
    ext e
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h2, h3⟩, ?_⟩
      rw [← hrank e (by simp [hC, h2, h3])]; exact h1
    · rintro ⟨⟨h2, h3⟩, h1⟩
      refine ⟨?_, h2, h3⟩
      rw [hrank e (by simp [hC, h2, h3])]; exact h1
  -- card of B = min K |C|
  have himg : C.image (fun e => (C.filter (fun f => better v f e)).card) = Finset.range C.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      simp only [Finset.mem_range]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨e, he, by simp [rs_better_irrefl]⟩
    · rw [Finset.card_image_of_injOn (rs_rank_injOn v C)]; simp
  have hBc : (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).card = min C.card K := by
    have h1 := Finset.card_image_of_injOn
      (s := C.filter (fun e => (C.filter (fun f => better v f e)).card < K))
      ((rs_rank_injOn v C).mono (by intro e he; simp only [Finset.coe_filter, Set.mem_setOf_eq] at he; exact he.1))
    have hfi : (C.filter (fun e => (C.filter (fun f => better v f e)).card < K)).image
        (fun e => (C.filter (fun f => better v f e)).card) =
        (C.image (fun e => (C.filter (fun f => better v f e)).card)).filter (fun x => x < K) := by
      ext x; simp only [Finset.mem_image, Finset.mem_filter]; constructor
      · rintro ⟨e, ⟨he, hk⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hk⟩
      · rintro ⟨⟨e, he, rfl⟩, hk⟩; exact ⟨e, ⟨he, hk⟩, rfl⟩
    rw [← h1, hfi, himg]
    have : (Finset.range C.card).filter (fun x => x < K) = Finset.range (min C.card K) := by
      ext x; simp [Finset.mem_filter, Finset.mem_range]
    rw [this, Finset.card_range]
  rw [hB, hBc]
  set T : Finset (Fin n) := Finset.univ.filter (fun e => inSample π τ e) with hT
  have hA : reservationStart v π τ K i ≤ (T.filter (fun e => (T.filter (fun f => better v f e)).card < K)).card := by
    unfold reservationStart
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    have he' := he.2.1
    unfold sampleTop at he'
    refine ⟨he'.1, ?_⟩
    have := he'.2
    convert this using 2
    ext f; simp [Finset.mem_filter]
  have hA2 : reservationStart v π τ K i ≤ C.card := by
    unfold reservationStart
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC]
    exact he.2.2
  have := rs_top_card_le v T K
  omega

end SecretaryWD.Weighted

open SecretaryWD.Weighted


theorem solution {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (hτ : τ ≤ n) (i : ℤ) :
    reservationStart v π τ K i ≤ optimalStart (K := K) v i := by
  exact rs_core v π τ i
