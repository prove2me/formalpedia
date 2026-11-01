-- Prove2me | solution 1 for ReferralPriority.Optimal.proposition_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:24:22.323995+00:00
-- url     : https://prove2.me/submissions/a6fd1798-a0f5-4133-b4f0-5d5e0642a0d3

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model
import Theorems.Thm_ReferralPriority_Optimal_rFB_solves_A2

open ReferralPriority.Optimal

/-- From IR and (6a): the referral effort constraint V − rk − c/(µ(1−rα) − Λα) ≥ 0, cleared. -/
theorem rp_p1i_constraint (E : Env) (hc : 0 < E.c) (Lam W1 W0 r α : ℝ)
    (h : FBFeasible E Lam W1 W0 r α) :
    0 < E.mu * (1 - r * α) - Lam * α ∧
      E.c ≤ (E.V - E.k * r) * (E.mu * (1 - r * α) - Lam * α) := by
  obtain ⟨-, -, -, -, hIR, hOA, -, -, hst⟩ := h
  unfold Stable at hst
  have hden : 0 < E.mu * (1 - r * α) - Lam * α := by linarith
  refine ⟨hden, ?_⟩
  unfold IR payoff at hIR
  unfold OA6a at hOA
  rw [div_le_iff₀ hden] at hOA
  nlinarith

theorem solution (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    0 < rFB E Lam ∧
      IsGreatest (FBValues E Lam) (throughput Lam (rFB E Lam) 1) ∧
      ∀ W1 W0 r α : ℝ, FBFeasible E Lam W1 W0 r α →
        throughput Lam r α = throughput Lam (rFB E Lam) 1 →
          α = 1 ∧ r = rFB E Lam ∧ WorkConserving E Lam W1 W0 r α := by
  obtain ⟨hr0, hr1, hD, hA2⟩ := rFB_solves_A2 E hS Lam hL0 hL1
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  set rF := rFB E Lam with hrF
  set D := E.mu * (1 - rF) - Lam with hD_def
  have hcD : E.c = (E.V - rF * E.k) * D := by
    have : E.c / D = E.V - rF * E.k := by linarith
    rw [← this]; field_simp
  have hVr : 0 < E.V - rF * E.k := by
    have : 0 < E.c / D := div_pos hc hD
    linarith
  have h1rF : 0 < 1 - rF := by linarith
  -- key: every FB-feasible tuple has α (1 - rF) ≤ 1 - rα, and the equality analysis
  have key : ∀ W1 W0 r α : ℝ, FBFeasible E Lam W1 W0 r α → α * (1 - rF) ≤ 1 - r * α := by
    intro W1 W0 r α hF
    obtain ⟨hden, hcon⟩ := rp_p1i_constraint E hc Lam W1 W0 r α hF
    obtain ⟨-, -, ⟨hr0', hr1'⟩, ⟨hα0, hα1⟩, -⟩ := hF
    by_contra hlt
    push Not at hlt
    set y := 1 - r * α with hy
    have hVkr : 0 < E.V - E.k * r := by
      by_contra hn; push Not at hn; nlinarith
    have hyF : y < 1 - rF := lt_of_lt_of_le hlt (by nlinarith)
    have hxr : r * α ≤ r := by nlinarith
    have hrr : rF < r := by linarith
    -- den (1 - rF) < y D
    have h1 : (E.mu * y - Lam * α) * (1 - rF) < y * D := by
      rw [hD_def]
      have : Lam * y < Lam * (α * (1 - rF)) := mul_lt_mul_of_pos_left hlt hL0
      nlinarith
    have h2 : E.c * (1 - rF) ≤ (E.V - E.k * r) * ((E.mu * y - Lam * α) * (1 - rF)) := by
      have := mul_le_mul_of_nonneg_right hcon h1rF.le
      rw [hy]; nlinarith
    have h3 : (E.V - E.k * r) * ((E.mu * y - Lam * α) * (1 - rF)) < (E.V - E.k * r) * (y * D) :=
      mul_lt_mul_of_pos_left h1 hVkr
    have hy0 : 0 < y := by
      by_contra hn; push Not at hn
      have : E.mu * y - Lam * α ≤ 0 := by nlinarith
      rw [hy] at this; linarith
    have h4 : (E.V - E.k * r) * y < (E.V - rF * E.k) * (1 - rF) := by
      have e1 : E.V - E.k * r < E.V - rF * E.k := by nlinarith
      calc (E.V - E.k * r) * y < (E.V - rF * E.k) * y := mul_lt_mul_of_pos_right e1 hy0
        _ < (E.V - rF * E.k) * (1 - rF) := mul_lt_mul_of_pos_left hyF hVr
    have h5 := mul_lt_mul_of_pos_right h4 hD
    rw [hcD] at h2
    nlinarith
  -- the first-best tuple
  have hmem : throughput Lam rF 1 ∈ FBValues E Lam := by
    have hDr : D ≤ E.mu * (1 - rF) - Lam * rF := by rw [hD_def]; nlinarith
    refine ⟨1 / D, 1 / D, rF, 1, ⟨by positivity, by positivity, ⟨hr0.le, hr1.le⟩,
      ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · unfold IR payoff
      have : E.c * (rF * 1 * (1 / D) + (1 - rF * 1) * (1 / D)) = E.c / D := by field_simp; ring
      rw [this]; linarith
    · unfold OA6a; simp only [mul_one]; rw [← hD_def]; apply le_of_eq; ring
    · unfold OA6b; simp only [mul_one, one_pow]
      exact one_div_le_one_div_of_le hD hDr
    · unfold OA6c; simp only [mul_one]
      exact one_div_le_one_div_of_le hD (by rw [hD_def]; nlinarith)
    · unfold Stable; simp only [mul_one]; linarith
  refine ⟨hr0, ⟨hmem, ?_⟩, ?_⟩
  · rintro x ⟨W1, W0, r, α, hF, rfl⟩
    have hk' := key W1 W0 r α hF
    obtain ⟨hden, -⟩ := rp_p1i_constraint E hc Lam W1 W0 r α hF
    obtain ⟨-, -, ⟨hr0', hr1'⟩, ⟨hα0, hα1⟩, -⟩ := hF
    have hy0 : 0 < 1 - r * α := by nlinarith
    unfold throughput
    rw [mul_one, mul_one, div_le_div_iff₀ hy0 h1rF]
    nlinarith
  · intro W1 W0 r α hF hT
    have hk' := key W1 W0 r α hF
    obtain ⟨hden, hcon⟩ := rp_p1i_constraint E hc Lam W1 W0 r α hF
    have hF' := hF
    obtain ⟨-, -, ⟨hr0', hr1'⟩, ⟨hα0, hα1⟩, hIR, hOA, -⟩ := hF
    have hy0 : 0 < 1 - r * α := by nlinarith
    unfold throughput at hT
    rw [mul_one, mul_one, div_eq_div_iff hy0.ne' h1rF.ne'] at hT
    have hyeq : α * (1 - rF) = 1 - r * α := by
      have := mul_left_cancel₀ hL0.ne' (by linarith : Lam * (α * (1 - rF)) = Lam * (1 - r * α))
      exact this
    set y := 1 - r * α with hy
    have hdeneq : (E.mu * y - Lam * α) * (1 - rF) = y * D := by
      rw [hD_def, ← hyeq]; ring
    have h2 : E.c * (1 - rF) ≤ (E.V - E.k * r) * (y * D) := by
      rw [← hdeneq]
      have := mul_le_mul_of_nonneg_right hcon h1rF.le
      calc E.c * (1 - rF) ≤ (E.V - E.k * r) * (E.mu * (1 - r * α) - Lam * α) * (1 - rF) := this
        _ = _ := by rw [hy]; ring
    rw [hcD] at h2
    have h3 : (E.V - rF * E.k) * (1 - rF) ≤ (E.V - E.k * r) * y := by
      have : (E.V - rF * E.k) * (1 - rF) * D ≤ (E.V - E.k * r) * y * D := by
        have e1 : (E.V - rF * E.k) * (1 - rF) * D = (E.V - rF * E.k) * D * (1 - rF) := by ring
        have e2 : (E.V - E.k * r) * y * D = (E.V - E.k * r) * (y * D) := by ring
        linarith
      exact le_of_mul_le_mul_right this hD
    have hyF : y ≤ 1 - rF := by rw [← hyeq]; exact mul_le_of_le_one_left h1rF.le hα1
    have hrr : rF ≤ r := by
      have : r * α ≤ r := mul_le_of_le_one_right hr0' hα1
      linarith
    have hVkr : 0 < E.V - E.k * r := by
      by_contra hn; push Not at hn
      have := mul_le_mul_of_nonneg_right hn hden.le
      linarith
    have hreq : r = rF := by
      by_contra hne
      have hlt : rF < r := lt_of_le_of_ne hrr (Ne.symm hne)
      have e1 : E.V - E.k * r < E.V - rF * E.k := by
        have := mul_lt_mul_of_pos_left hlt hkpos
        linarith
      have : (E.V - E.k * r) * y < (E.V - rF * E.k) * (1 - rF) := by
        calc (E.V - E.k * r) * y < (E.V - rF * E.k) * y := mul_lt_mul_of_pos_right e1 hy0
          _ ≤ (E.V - rF * E.k) * (1 - rF) := mul_le_mul_of_nonneg_left hyF hVr.le
      linarith
    subst hreq
    have hyge : 1 - rF ≤ y := by
      have : (E.V - rF * E.k) * (1 - rF) ≤ (E.V - rF * E.k) * y := by
        have e : E.V - E.k * rF = E.V - rF * E.k := by ring
        rw [e] at h3; exact h3
      exact le_of_mul_le_mul_left this hVr
    have hα : α = 1 := by
      have : (1 - rF) * 1 ≤ (1 - rF) * α := by linarith [hyge, hyeq]
      have := le_of_mul_le_mul_left this h1rF
      linarith
    subst hα
    refine ⟨rfl, rfl, ?_⟩
    unfold WorkConserving
    unfold OA6a at hOA
    unfold IR payoff at hIR
    simp only [mul_one] at hOA hIR ⊢
    rw [← hD_def] at hOA ⊢
    apply le_antisymm _ hOA
    have : E.c * (rF * W1 + (1 - rF) * W0) ≤ E.c * (1 / D) := by
      have : E.c * (1 / D) = E.V - rF * E.k := by rw [hcD]; field_simp
      rw [this]; linarith
    exact le_of_mul_le_mul_left this hc
