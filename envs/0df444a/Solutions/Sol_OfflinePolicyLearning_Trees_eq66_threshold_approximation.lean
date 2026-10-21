-- Prove2me | solution 1 for OfflinePolicyLearning.Trees.eq66_threshold_approximation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:14:25.676991+00:00
-- url     : https://prove2.me/submissions/872d3912-4142-4daf-8eec-277b46c4d33c

import Mathlib
set_option autoImplicit false

theorem solution (L : ℕ) (hL : 1 ≤ L) (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : 1 ≤ m) (r : Fin m → ℝ) :
    ∃ b' : Fin ⌈(L : ℝ) / ε⌉₊ → ℝ, ∀ b : ℝ, ∃ i,
      (1 / (m : ℝ)) * ((Finset.univ.filter fun j => ¬ (r j < b ↔ r j < b' i)).card : ℝ)
        ≤ ε / L := by
  classical
  set N : ℝ → ℕ := fun x => (Finset.univ.filter fun j => r j < x).card with hN
  have hNle : ∀ x, N x ≤ m := by
    intro x
    have := Finset.card_le_univ (Finset.univ.filter fun j => r j < x)
    simpa using this
  have hbest : ∀ t : ℕ, ∃ c : ℝ, N c ≤ t ∧ ∀ b, N b ≤ t → N b ≤ N c := by
    intro t
    obtain ⟨b0, hb0⟩ := (Set.finite_range r).bddBelow
    have hN0 : N b0 = 0 := by
      simp only [hN, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      exact not_lt.mpr (hb0 ⟨j, rfl⟩)
    let P : ℕ → Prop := fun n => ∃ b, N b = n
    have hP0 : P 0 := ⟨b0, hN0⟩
    have hspec : P (Nat.findGreatest P t) := Nat.findGreatest_spec (Nat.zero_le t) hP0
    obtain ⟨c, hc⟩ := hspec
    refine ⟨c, ?_, ?_⟩
    · rw [hc]; exact Nat.findGreatest_le t
    · intro b hb
      rw [hc]
      exact Nat.le_findGreatest hb ⟨b, rfl⟩
  have hdist : ∀ x y : ℝ, N x ≤ N y →
      (Finset.univ.filter fun j => ¬ (r j < x ↔ r j < y)).card ≤ N y - N x := by
    intro x y hxy
    have hmono : ∀ x y : ℝ, x ≤ y → N x ≤ N y := by
      intro x y h
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_lt_of_le hj h
    rcases le_total x y with h | h
    · have hsub : (Finset.univ.filter fun j => r j < x) ⊆ (Finset.univ.filter fun j => r j < y) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact lt_of_lt_of_le hj h
      calc _ ≤ ((Finset.univ.filter fun j => r j < y) \ (Finset.univ.filter fun j => r j < x)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at hj ⊢
            have h3 : r j < x → r j < y := fun hh => lt_of_lt_of_le hh h
            tauto
        _ = N y - N x := Finset.card_sdiff_of_subset hsub
    · have hsub : (Finset.univ.filter fun j => r j < y) ⊆ (Finset.univ.filter fun j => r j < x) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact lt_of_lt_of_le hj h
      have hyx := hmono y x h
      calc _ ≤ ((Finset.univ.filter fun j => r j < x) \ (Finset.univ.filter fun j => r j < y)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at hj ⊢
            have h3 : r j < y → r j < x := fun hh => lt_of_lt_of_le hh h
            tauto
        _ = N x - N y := Finset.card_sdiff_of_subset hsub
        _ ≤ N y - N x := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set w : ℕ := ⌊(m : ℝ) * ε / L⌋₊ with hw
  set K : ℕ := ⌈(L : ℝ) / ε⌉₊ with hK
  let T : ℕ → ℕ := fun i => min m ((i + 1) * (w + 1) - 1)
  refine ⟨fun i => (hbest (T i)).choose, ?_⟩
  intro b
  set a := N b with ha
  have ham : a ≤ m := hNle b
  set q := a / (w + 1) with hq
  have hdm : (w + 1) * q + a % (w + 1) = a := Nat.div_add_mod a (w + 1)
  have hmod : a % (w + 1) < w + 1 := Nat.mod_lt _ (Nat.succ_pos w)
  have hqK : q < K := by
    by_contra hcon
    push_neg at hcon
    have h1 : (L : ℝ) / ε ≤ (q : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hcon)
    have h2 : (m : ℝ) * ε / L < (w : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((w + 1) * q : ℕ) ≤ m := by omega
    have h4 : (((w : ℝ) + 1) * q) ≤ m := by exact_mod_cast h3
    have hLe : (0 : ℝ) < L / ε := div_pos hLpos hε
    have h5 : (L / ε) * ((m : ℝ) * ε / L) < (L / ε) * ((w : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hLe
    have h6 : (L / ε) * ((m : ℝ) * ε / L) = m := by field_simp
    have h7 : (L / ε) * ((w : ℝ) + 1) ≤ q * ((w : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  refine ⟨⟨q, hqK⟩, ?_⟩
  obtain ⟨hc1, hc2⟩ := (hbest (T q)).choose_spec
  set c := (hbest (T q)).choose with hc
  have hTa : a ≤ T q := by
    have : (q + 1) * (w + 1) = (w + 1) * q + (w + 1) := by ring
    simp only [T]
    rw [this]
    generalize (w + 1) * q = P at *
    omega
  have hTw : T q - a ≤ w := by
    have : (q + 1) * (w + 1) = (w + 1) * q + (w + 1) := by ring
    simp only [T]
    rw [this]
    generalize (w + 1) * q = P at *
    omega
  have hac : a ≤ N c := hc2 b (le_trans (le_refl _) hTa)
  have hcard := hdist b c hac
  have hcw : (Finset.univ.filter fun j => ¬ (r j < b ↔ r j < c)).card ≤ w := by
    have : N c - a ≤ T q - a := by omega
    omega
  have hwle : (w : ℝ) ≤ (m : ℝ) * ε / L := Nat.floor_le (by positivity)
  have hcr : ((Finset.univ.filter fun j => ¬ (r j < b ↔ r j < c)).card : ℝ) ≤ (m : ℝ) * ε / L :=
    le_trans (by exact_mod_cast hcw) hwle
  calc (1 / (m : ℝ)) * ((Finset.univ.filter fun j => ¬ (r j < b ↔ r j < c)).card : ℝ)
      ≤ (1 / (m : ℝ)) * ((m : ℝ) * ε / L) :=
        mul_le_mul_of_nonneg_left hcr (by positivity)
    _ = ε / L := by field_simp
