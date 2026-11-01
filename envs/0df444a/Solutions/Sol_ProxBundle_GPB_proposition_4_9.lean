-- Prove2me | solution 1 for ProxBundle.GPB.proposition_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:44:10.347755+00:00
-- url     : https://prove2.me/submissions/3ba393b0-1bce-4408-a0a3-c6b35ae91947

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_proposition_4_3
import Theorems.Thm_ProxBundle_GPB_proposition_4_8
import Theorems.Thm_ProxBundle_GPB_lemma_4_6

open ProxBundle.GPB

theorem solution {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε : ℝ)
    (x0 x0s : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hpos : 0 < Mf ^ 2 + ε * Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hx0s : P.IsNearestOpt x0 x0s) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hrun : IsRun P μ lam ε (tau38 μ lam ε Mf Lf) x0 R) :
    ∃ j : ℕ, (j : ℝ) ≤
      ((⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
        max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) + 1) *
        (serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1) ∧
      P.φ (R.y j) - P.φ x0s ≤ ε := by
  classical
  obtain ⟨hM, hL, hA3b, hminle⟩ := hmin
  have hMfL := hminle Mf Lf hMf hLf hA3
  have hlm : 0 < 1 + lam * μ := by positivity
  have hqpos : 0 < (1 + lam * μ) * ε / (8 * lam * (Mf ^ 2 + ε * Lf)) := by positivity
  set τ := tau38 μ lam ε Mf Lf with hτdef
  have hτ0 : 0 < τ := by rw [hτdef, tau38]; positivity
  have hτ1 : τ < 1 := by
    rw [hτdef, tau38]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have key : τ / (1 - τ) = 8 * lam * (Mf ^ 2 + ε * Lf) / ((1 + lam * μ) * ε) := by
    rw [hτdef, tau38]
    have h8 : (8 * lam * (Mf ^ 2 + ε * Lf)) ≠ 0 := by positivity
    have h9 : (1 + lam * μ) * ε ≠ 0 := by positivity
    field_simp
    ring
  have h29 : Cond29 μ lam ε τ Mbar Lbar := by
    unfold Cond29
    rw [key]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  -- existence of a next serious index (from Lemma 4.6)
  have hnext : ∀ j0 : ℕ, ∃ j, j0 < j ∧ R.t P lam j ≤ ε / 2 := by
    intro j0
    by_contra hcon
    push Not at hcon
    have hcontr : ∀ m : ℕ, R.t P lam (j0 + 1 + m) - ε / 4 ≤
        τ ^ m * (R.t P lam (j0 + 1) - ε / 4) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h46 := lemma_4_6 P μ Mbar Lbar lam ε τ x0 R hμ hM hL hA1 hA3b hlam hε
          hτ0 hτ1 h29 hx0 hrun (j0 + 1 + m) (by omega) (hcon _ (by omega))
        rw [show j0 + 1 + (m + 1) = j0 + 1 + m + 1 by ring, pow_succ]
        calc _ ≤ τ * (R.t P lam (j0 + 1 + m) - ε / 4) := h46
          _ ≤ τ * (τ ^ m * (R.t P lam (j0 + 1) - ε / 4)) :=
              mul_le_mul_of_nonneg_left ih hτ0.le
          _ = _ := by ring
    have ha : 0 < R.t P lam (j0 + 1) - ε / 4 := by
      have := hcon (j0 + 1) (by omega); linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (show 0 < ε / 4 / (R.t P lam (j0 + 1) - ε / 4) by positivity) hτ1
    have h1 := hcontr m
    have h2 := hcon (j0 + 1 + m) (by omega)
    rw [lt_div_iff₀ ha] at hm
    linarith
  let nxt : ℕ → ℕ := fun j0 => Nat.find (hnext j0)
  have nxt_spec : ∀ j0, j0 < nxt j0 ∧ R.t P lam (nxt j0) ≤ ε / 2 :=
    fun j0 => Nat.find_spec (hnext j0)
  have nxt_min : ∀ j0 i, j0 < i → i < nxt j0 → ε / 2 < R.t P lam i := by
    intro j0 i h1 h2
    have := Nat.find_min (hnext j0) h2
    push Not at this
    exact this h1
  let s : ℕ → ℕ := fun k => nxt^[k] 0
  have hs0 : s 0 = 0 := rfl
  have hs_succ : ∀ k, s (k + 1) = nxt (s k) := fun k =>
    Function.iterate_succ_apply' nxt k 0
  have ht0 : R.t P lam 0 = 0 := by simp [Run.t]
  have hser : ∀ k, R.t P lam (s k) ≤ ε / 2 := by
    intro k
    cases k with
    | zero => rw [hs0, ht0]; positivity
    | succ k => rw [hs_succ]; exact (nxt_spec _).2
  -- facts about the run
  have hΓ : ∀ j, 1 ≤ j → P.ConvBar μ (R.Γ j) ∧ ∀ u ∈ P.D, R.Γ j u ≤ P.φ u := by
    intro j hj
    obtain ⟨h1, h2, -, -, -⟩ := hrun.2.2 j hj
    by_cases ht : R.t P lam (j - 1) ≤ ε / 2
    · obtain ⟨-, hc, hu⟩ := h1 ht
      exact ⟨hc, fun u hu' => (hu u hu').2⟩
    · obtain ⟨hc, hu, -⟩ := (h2 (lt_of_not_ge ht)).2
      exact ⟨hc, hu⟩
  have hxD : ∀ i, R.x i ∈ P.D := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hrun.1]; exact hx0
    · exact ((hrun.2.2 i hi).2.2.1).1
  have hyD : ∀ j, R.y j ∈ P.D := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hrun.2.1]; exact hx0
    · obtain ⟨i, -, hi⟩ := (hrun.2.2 j hj).2.2.2.1
      rw [hi]; exact hxD i
  -- prox centre inside a cycle
  have hxc : ∀ j0, R.t P lam j0 ≤ ε / 2 → ∀ m, j0 + 1 ≤ m → m ≤ nxt j0 →
      R.xc m = R.x j0 := by
    intro j0 hj0 m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      exact (((hrun.2.2 (j0 + 1) (by omega)).1) (by simpa using hj0)).1
    | succ m hm ih =>
      intro hle
      have hnull : ε / 2 < R.t P lam m := nxt_min j0 m (by omega) (by omega)
      have := ((hrun.2.2 (m + 1) (by omega)).2.1) (by simpa using hnull)
      rw [this.1]
      simpa using ih (by omega)
  have hhat : IsHat P μ lam ε x0 (fun k => R.x (s k)) (fun k => R.y (s k))
      (fun k => R.Γ (s k)) := by
    refine ⟨by simp only [hs0]; exact hrun.1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hlt := (nxt_spec (s k')).1
    have hs1 : 1 ≤ s (k' + 1) := by rw [hs_succ]; omega
    have hxc' : R.xc (s (k' + 1)) = R.x (s k') := by
      rw [hs_succ]; exact hxc (s k') (hser k') _ (by omega) le_rfl
    obtain ⟨hc, hle⟩ := hΓ _ hs1
    refine ⟨hc, hle, ?_, hyD _, ?_⟩
    · have := (hrun.2.2 _ hs1).2.2.1
      rwa [hxc'] at this
    · have ht := hser (k' + 1)
      unfold Run.t at ht
      rw [if_neg (by omega)] at ht
      unfold Run.m at ht
      rw [hxc'] at ht
      exact ht
  obtain ⟨K, hK1, hKsol, hKbefore, hKle, -⟩ :=
    proposition_4_3 P μ lam ε x0 x0s _ _ _ hμ hA1 hlam hε hhat hx0s
  set C : ℝ := (⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
        max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) + 1 with hC
  have hC0 : 0 ≤ C := by
    have hlmu : 0 ≤ lamMu μ lam := by unfold lamMu; positivity
    have : 0 ≤ (1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
        max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0 := by
      apply mul_nonneg (by positivity) (le_max_right _ _)
    have : (0 : ℝ) ≤ (⌈(1 + 8 * lamMu μ lam * (Mf ^ 2 + ε * Lf) / ε) *
        max (Real.log (4 * tbar Mbar Lbar lam ‖x0 - x0s‖ / ε)) 0⌉ : ℝ) :=
      by exact_mod_cast Int.ceil_nonneg this
    rw [hC]; linarith
  have hgap : ∀ i, i < K → ((s (i + 1) - s i : ℕ) : ℝ) ≤ C := by
    intro i hi
    have hb : s i = 0 ∨ ε < P.φ (R.y (s i)) - P.φ x0s := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · left; rfl
      · right; exact hKbefore i hi0 hi
    obtain ⟨j1, hj1, hj1s, hj1btw, -, hb2⟩ :=
      proposition_4_8 P μ Mbar Lbar lam ε τ x0 x0s R hμ hM hL hA1 hA3b hlam hε
        hτ0 hτ1 h29 hx0 hx0s hrun (s i) (hser i) hb
    have heq : nxt (s i) = j1 := by
      apply le_antisymm
      · exact Nat.find_min' _ ⟨hj1, hj1s⟩
      · by_contra hlt
        push Not at hlt
        have := hj1btw (nxt (s i)) (nxt_spec _).1 hlt
        linarith [(nxt_spec (s i)).2]
    rw [hs_succ, heq]
    exact hb2 Mf Lf hpos rfl
  have hsle : ∀ i, i ≤ K → (s i : ℝ) ≤ i * C := by
    intro i
    induction i with
    | zero => intro _; simp [hs0]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hgap i (by omega)
      have hmono : s i ≤ s (i + 1) := by rw [hs_succ]; exact (nxt_spec _).1.le
      rw [Nat.cast_sub hmono] at h2
      push_cast
      linarith
  refine ⟨s K, ?_, hKsol⟩
  calc (s K : ℝ) ≤ K * C := hsle K le_rfl
    _ ≤ (serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1) * C :=
        mul_le_mul_of_nonneg_right hKle hC0
    _ = C * (serBound μ lam ε (‖x0 - x0s‖ ^ 2) + 1) := by ring
