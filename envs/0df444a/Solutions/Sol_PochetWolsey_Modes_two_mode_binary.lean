-- Prove2me | solution 1 for PochetWolsey.Modes.two_mode_binary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:07:56.33299+00:00
-- url     : https://prove2.me/submissions/d8c7729c-2bb0-443e-a55a-56dc4e7c882d

import Mathlib

lemma s225mb_sum_mem {k : ℕ} (L : List (Fin k)) (h : L.Nodup) :
    ∑ i, (if i ∈ L then (1 : ℝ) else 0) = L.length := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i => i ∈ L)) = L.toFinset := by
    ext i; simp
  rw [this, List.toFinset_card_of_nodup h]

lemma s225mb_two {α : Type*} (L : List α) (hL : L ≠ []) (hlen : L.length ≤ 2) :
    (∃ x, L = [x]) ∨ (∃ x y, L = [x, y]) := by
  match L, hL, hlen with
  | [x], _, _ => exact Or.inl ⟨x, rfl⟩
  | [x, y], _, _ => exact Or.inr ⟨x, y, rfl⟩
  | _ :: _ :: _ :: _, _, h => simp at h

lemma s225mb_link {α : Type*} (L L' : List α) (hL : L ≠ []) (hlen : L.length ≤ 2)
    (hnd' : L'.Nodup) (hlink : L.getLast? = L'.head?) (i : α) :
    (i ∈ L' → i ∉ L'.tail → i ∈ L) ∧ (i ∈ L.tail → i ∈ L' ∧ i ∉ L'.tail) := by
  rcases L' with _ | ⟨c, l⟩
  · rcases s225mb_two L hL hlen with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ <;> simp at hlink
  · have hc : c ∉ l := (List.nodup_cons.mp hnd').1
    rcases s225mb_two L hL hlen with ⟨x, rfl⟩ | ⟨x, y, rfl⟩
    · simp at hlink
      subst hlink
      refine ⟨?_, ?_⟩
      · intro h1 h2
        simp only [List.tail_cons] at h2
        rcases List.mem_cons.mp h1 with h | h
        · simp [h]
        · exact absurd h h2
      · simp
    · simp at hlink
      subst hlink
      refine ⟨?_, ?_⟩
      · intro h1 h2
        simp only [List.tail_cons] at h2
        rcases List.mem_cons.mp h1 with h | h
        · simp [h]
        · exact absurd h h2
      · intro h
        simp only [List.tail_cons, List.mem_singleton] at h
        subst h
        exact ⟨List.mem_cons_self, hc⟩

lemma s225mb_bin (x : ℝ) (P : Prop) [Decidable P] (hx : x = 0 ∨ x = 1) (h : x = 1 ↔ P) :
    x = if P then 1 else 0 := by
  split_ifs with hP
  · exact h.mpr hP
  · rcases hx with hx | hx
    · exact hx
    · exact absurd (h.mp hx) hP

theorem solution (m n : ℕ) :
    {p : (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) | ∃ s : Fin (n + 1) → List (Fin (m + 1)),
      (∀ t, s t ≠ [] ∧ (s t).Nodup) ∧
      (∀ t : Fin n, (s t.castSucc).getLast? = (s t.succ).head?) ∧ (∀ t, (s t).length ≤ 2) ∧ p = ((fun i t => if i ∈ s t then (1 : ℝ) else 0), (fun i t => if i ∈ (s t).tail then (1 : ℝ) else 0))} =
    {p | (∀ i, (∀ t, p.1 i t = 0 ∨ p.1 i t = 1)) ∧ (∀ i, (∀ t, p.2 i t = 0 ∨ p.2 i t = 1)) ∧
    (∀ t, ∑ i, (p.1 i t - p.2 i t) = 1) ∧
    (∀ t, ∑ i, p.2 i t ≤ 1) ∧
    (∀ i t, p.2 i t ≤ p.1 i t) ∧
    (∀ i (t : Fin n), p.2 i t.succ ≥ p.1 i t.succ - p.1 i t.castSucc) ∧
    (∀ i (t : Fin n), p.2 i t.succ + p.2 i t.castSucc ≤ p.1 i t.succ)} := by
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hne, hlink, hlen, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t; dsimp only; split_ifs <;> simp
    · intro i t; dsimp only; split_ifs <;> simp
    · intro t
      dsimp only
      have hpos := List.length_pos_of_ne_nil (hne t).1
      rw [Finset.sum_sub_distrib, s225mb_sum_mem _ (hne t).2,
        s225mb_sum_mem _ ((hne t).2.sublist (List.tail_sublist _)), List.length_tail,
        Nat.cast_sub (by omega)]
      ring
    · intro t
      dsimp only
      rw [s225mb_sum_mem _ ((hne t).2.sublist (List.tail_sublist _)), List.length_tail]
      have := hlen t
      exact_mod_cast (by omega : (s t).length - 1 ≤ 1)
    · intro i t
      dsimp only
      have H3 := @List.mem_of_mem_tail _ i (s t)
      split_ifs <;> first | (exfalso; tauto) | norm_num
    · intro i t
      dsimp only
      obtain ⟨H1, -⟩ := s225mb_link _ _ (hne t.castSucc).1 (hlen t.castSucc) (hne t.succ).2
        (hlink t) i
      split_ifs <;> first | (exfalso; tauto) | norm_num
    · intro i t
      dsimp only
      obtain ⟨-, H2⟩ := s225mb_link _ _ (hne t.castSucc).1 (hlen t.castSucc) (hne t.succ).2
        (hlink t) i
      have H3 := @List.mem_of_mem_tail _ i (s t.succ)
      split_ifs <;> first | (exfalso; tauto) | norm_num
  · rintro ⟨hb1, hb2, hsum, hsum2, hle, h6, h7⟩
    have hp1le : ∀ i t, p.1 i t ≤ 1 := fun i t => by rcases hb1 i t with h | h <;> rw [h] <;> norm_num
    have hp2nn : ∀ i t, 0 ≤ p.2 i t := fun i t => by rcases hb2 i t with h | h <;> rw [h] <;> norm_num
    have hex : ∀ t, ∃ a, p.1 a t = 1 ∧ p.2 a t = 0 := by
      intro t
      by_contra hcon
      push Not at hcon
      have hz : ∀ i, p.1 i t - p.2 i t = 0 := by
        intro i
        rcases hb1 i t with h1 | h1
        · rcases hb2 i t with h2 | h2
          · rw [h1, h2]; norm_num
          · have := hle i t; rw [h1, h2] at this; norm_num at this
        · rcases hb2 i t with h2 | h2
          · exact absurd h2 (hcon i h1)
          · rw [h1, h2]; norm_num
      have := hsum t
      rw [Finset.sum_eq_zero (fun i _ => hz i)] at this
      norm_num at this
    choose a ha using hex
    have huniq : ∀ t i, p.1 i t = 1 → p.2 i t = 0 → i = a t := by
      intro t i h1 h2
      by_contra hne
      have hnn : ∀ j, 0 ≤ p.1 j t - p.2 j t := fun j => sub_nonneg.mpr (hle j t)
      have hs : p.1 i t - p.2 i t + (p.1 (a t) t - p.2 (a t) t) ≤ ∑ j, (p.1 j t - p.2 j t) := by
        rw [← Finset.sum_pair (f := fun j => p.1 j t - p.2 j t) hne]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
      rw [h1, h2, (ha t).1, (ha t).2, hsum t] at hs
      norm_num at hs
    have huniq2 : ∀ t i j, p.2 i t = 1 → p.2 j t = 1 → i = j := by
      intro t i j hi hj
      by_contra hne
      have hs : p.2 i t + p.2 j t ≤ ∑ k, p.2 k t := by
        rw [← Finset.sum_pair (f := fun k => p.2 k t) hne]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => hp2nn k t)
      have := hsum2 t
      rw [hi, hj] at hs
      linarith
    let s : Fin (n + 1) → List (Fin (m + 1)) := fun t =>
      if h : ∃ i, p.2 i t = 1 then [a t, h.choose] else [a t]
    have hhead : ∀ t, (s t).head? = some (a t) := by
      intro t; simp only [s]; split_ifs <;> rfl
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · intro t
      simp only [s]
      split_ifs with h
      · refine ⟨by simp, ?_⟩
        simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true]
        intro heq
        have := h.choose_spec
        rw [← heq, (ha t).2] at this
        norm_num at this
      · exact ⟨by simp, List.nodup_singleton _⟩
    · intro t
      rw [hhead]
      by_cases h : ∃ i, p.2 i t.castSucc = 1
      · have e : (s t.castSucc).getLast? = some h.choose := by
          simp only [s]; rw [dif_pos h]; rfl
        rw [e]
        have hb := h.choose_spec
        have h7b := h7 h.choose t
        rw [hb] at h7b
        have hp1 := hp1le h.choose t.succ
        have hp2 := hp2nn h.choose t.succ
        have e1 : p.1 h.choose t.succ = 1 := by linarith
        have e2 : p.2 h.choose t.succ = 0 := by linarith
        rw [huniq t.succ _ e1 e2]
      · have e : (s t.castSucc).getLast? = some (a t.castSucc) := by
          simp only [s]; rw [dif_neg h]; rfl
        rw [e]
        push Not at h
        set c := a t.succ
        have h6c := h6 c t
        rw [(ha t.succ).1, (ha t.succ).2] at h6c
        have hp1 := hp1le c t.castSucc
        have e1 : p.1 c t.castSucc = 1 := by linarith
        have e2 : p.2 c t.castSucc = 0 := by
          rcases hb2 c t.castSucc with h2 | h2
          · exact h2
          · exact absurd h2 (h c)
        rw [huniq t.castSucc c e1 e2]
    · intro t; simp only [s]; split_ifs <;> simp
    · refine Prod.ext (funext fun i => funext fun t => ?_) (funext fun i => funext fun t => ?_)
      · show p.1 i t = if i ∈ s t then 1 else 0
        apply s225mb_bin _ _ (hb1 i t)
        simp only [s]
        split_ifs with h
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
          constructor
          · intro h1
            rcases hb2 i t with h2 | h2
            · exact Or.inl (huniq t i h1 h2)
            · exact Or.inr (huniq2 t i _ h2 h.choose_spec)
          · rintro (rfl | rfl)
            · exact (ha t).1
            · have := hle h.choose t
              rw [h.choose_spec] at this
              linarith [hp1le h.choose t]
        · push Not at h
          simp only [List.mem_singleton]
          constructor
          · intro h1
            rcases hb2 i t with h2 | h2
            · exact huniq t i h1 h2
            · exact absurd h2 (h i)
          · rintro rfl; exact (ha t).1
      · show p.2 i t = if i ∈ (s t).tail then 1 else 0
        apply s225mb_bin _ _ (hb2 i t)
        simp only [s]
        split_ifs with h
        · simp only [List.tail_cons, List.mem_singleton]
          constructor
          · intro h2; exact huniq2 t i _ h2 h.choose_spec
          · rintro rfl; exact h.choose_spec
        · push Not at h
          simp only [List.tail_cons, List.not_mem_nil, iff_false]
          exact h i
