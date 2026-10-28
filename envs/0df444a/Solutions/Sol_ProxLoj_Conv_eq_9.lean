-- Prove2me | solution 1 for ProxLoj.Conv.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:58:40.741896+00:00
-- url     : https://prove2.me/submissions/e49a48f6-3136-48ba-82a6-e447fb0d2599

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open ProxLoj.Conv
open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hH1 : H1 f) (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x)
    (hne : ∀ k, x (k + 1) ≠ x k) (ℓ : ℝ) (hℓ : ℓ = (⨅ k, f (x k)).toReal)
    (θ M : ℝ) (N0 : ℕ) (hθ : 0 < θ ∧ θ < 1) (hM : 0 < M) (hN0 : 1 ≤ N0)
    (h8 : ∀ k, N0 ≤ k → ‖x (k + 1) - x k‖ ^ 2 / ‖x k - x (k - 1)‖ ≤
      M * (((f (x k)).toReal - ℓ) ^ (1 - θ) - ((f (x (k + 1))).toReal - ℓ) ^ (1 - θ))) :
    ∀ r : ℝ, 0 < r → r < 1 → ∀ N : ℕ, N0 ≤ N →
      ∑ k ∈ Finset.Icc N0 N, ‖x (k + 1) - x k‖ ≤
        r / (1 - r) * ‖x N0 - x (N0 - 1)‖ +
          M / (r * (1 - r)) *
            (((f (x N0)).toReal - ℓ) ^ (1 - θ) - ((f (x (N + 1))).toReal - ℓ) ^ (1 - θ)) := by
  intro r hr0 hr1 N hN
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, φ = fun k => ((f (x k)).toReal - ℓ) ^ (1 - θ) := ⟨_, rfl⟩
  have hφk : ∀ k, ((f (x k)).toReal - ℓ) ^ (1 - θ) = φ k := fun k => by rw [hφ]
  simp only [hφk] at h8 ⊢
  have hb : ∀ k, N0 ≤ k → ‖x (k + 1) - x k‖ ≤ r * ‖x k - x (k - 1)‖ + M * (φ k - φ (k + 1)) / r := by
    intro k hk
    have hk1 : x k ≠ x (k - 1) := by
      have := hne (k - 1)
      rwa [Nat.sub_add_cancel (by omega)] at this
    have ha : 0 < ‖x k - x (k - 1)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hk1)
    have h := h8 k hk
    rw [div_le_iff₀ ha] at h
    have hD : 0 ≤ M * (φ k - φ (k + 1)) := by
      by_contra hc
      push_neg at hc
      nlinarith [sq_nonneg ‖x (k + 1) - x k‖]
    have hbn := norm_nonneg (x (k + 1) - x k)
    obtain ⟨D, hDdef⟩ : ∃ D, D = M * (φ k - φ (k + 1)) := ⟨_, rfl⟩
    rw [← hDdef] at h hD ⊢
    have hDr : 0 ≤ D / r := div_nonneg hD hr0.le
    have hDr' : D / r * r = D := div_mul_cancel₀ D hr0.ne'
    by_contra hc
    push_neg at hc
    have h1 : (r * ‖x k - x (k - 1)‖ + D / r) ^ 2 < ‖x (k + 1) - x k‖ ^ 2 := by
      have : 0 ≤ r * ‖x k - x (k - 1)‖ + D / r := by positivity
      nlinarith
    nlinarith [mul_nonneg hr0.le ha.le, mul_nonneg (mul_nonneg hr0.le ha.le) hDr,
      sq_nonneg (r * ‖x k - x (k - 1)‖), sq_nonneg (D / r)]
  have Q : ∀ N, N0 ≤ N → ∑ k ∈ Finset.Icc N0 N, ‖x (k + 1) - x k‖ ≤
      r * (‖x N0 - x (N0 - 1)‖ + ∑ k ∈ Finset.Icc N0 N, ‖x (k + 1) - x k‖ - ‖x (N + 1) - x N‖)
        + M * (φ N0 - φ (N + 1)) / r := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have := hb N0 le_rfl
      linarith
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := hb (N + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      have e : M * (φ N0 - φ (N + 1 + 1)) / r = M * (φ N0 - φ (N + 1)) / r + M * (φ (N + 1) - φ (N + 1 + 1)) / r := by
        ring
      rw [e]
      linarith
  have hQ := Q N hN
  have hbN := norm_nonneg (x (N + 1) - x N)
  set S := ∑ k ∈ Finset.Icc N0 N, ‖x (k + 1) - x k‖
  have h1r : 0 < 1 - r := by linarith
  have hfin : (1 - r) * S ≤ r * ‖x N0 - x (N0 - 1)‖ + M * (φ N0 - φ (N + 1)) / r := by nlinarith
  have e2 : r / (1 - r) * ‖x N0 - x (N0 - 1)‖ + M / (r * (1 - r)) * (φ N0 - φ (N + 1))
      = (r * ‖x N0 - x (N0 - 1)‖ + M * (φ N0 - φ (N + 1)) / r) / (1 - r) := by
    field_simp
  rw [e2, le_div_iff₀ h1r]
  linarith
