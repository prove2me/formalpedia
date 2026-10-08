-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.mm1_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:59:32.688988+00:00
-- url     : https://prove2.me/submissions/028656c4-0c61-46c4-814b-03be6c319eb4

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

set_option autoImplicit false

open QueueingFundamentals.BirthDeath in
lemma mm1ss_rec (lam mu : ℝ) (hmu : 0 < mu) (p : ℕ → ℝ)
    (hb : IsBalanced (fun _ => lam) (fun _ => mu) p) : ∀ n, p n = (lam / mu) ^ n * p 0 := by
  have step : ∀ n : ℕ, mu * p (n + 1) = lam * p n := by
    intro n
    induction n with
    | zero => exact hb.2.symm
    | succ n ih =>
      have e := hb.1 (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at e
      linear_combination ih - e
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : p (n + 1) = (lam / mu) * p n := by
      rw [div_mul_eq_mul_div, eq_div_iff hmu.ne']
      linarith [step n]
    rw [h1, ih]; ring

open QueueingFundamentals.BirthDeath in
lemma mm1ss_geo (lam mu ρ : ℝ) (hmu : 0 < mu) (hρ : ρ = lam / mu) (hρ0 : 0 < ρ)
    (h1 : ρ < 1) : IsSteadyState (fun _ => lam) (fun _ => mu) (fun n => (1 - ρ) * ρ ^ n) := by
  have hl : lam = mu * ρ := by rw [hρ]; field_simp
  refine ⟨fun n => mul_nonneg (by linarith) (pow_nonneg hρ0.le n), ?_, ?_, ?_⟩
  · have hg := (hasSum_geometric_of_lt_one hρ0.le h1).mul_left (1 - ρ)
    have hne : (1 - ρ) ≠ 0 := by linarith
    rwa [mul_inv_cancel₀ hne] at hg
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [hl]; ring
  · simp only [pow_zero, pow_one]
    rw [hl]; ring

open QueueingFundamentals.BirthDeath in
lemma mm1ss_fwd (lam mu ρ : ℝ) (hmu : 0 < mu) (hρ : ρ = lam / mu) (hρ0 : 0 < ρ)
    (p : ℕ → ℝ) (hp : IsSteadyState (fun _ => lam) (fun _ => mu) p) :
    ρ < 1 ∧ ∀ n, p n = (1 - ρ) * ρ ^ n := by
  obtain ⟨_, hs, hb⟩ := hp
  have hrec : ∀ n, p n = ρ ^ n * p 0 := by
    intro n; rw [hρ]; exact mm1ss_rec lam mu hmu p hb n
  have hs' : HasSum (fun n => ρ ^ n * p 0) 1 := by
    have : p = fun n => ρ ^ n * p 0 := funext hrec
    rw [this] at hs; exact hs
  have hp0 : p 0 ≠ 0 := by
    intro h0
    rw [h0] at hs'
    simp only [mul_zero] at hs'
    exact one_ne_zero (hs'.unique hasSum_zero)
  have hlt : ρ < 1 := by
    have hsum : Summable (fun n : ℕ => ρ ^ n) := (summable_mul_right_iff hp0).1 hs'.summable
    rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_pos hρ0] at hsum
    exact hsum
  have hg := (hasSum_geometric_of_lt_one hρ0.le hlt).mul_right (p 0)
  have heq := hg.unique hs'
  have hne : (1 - ρ) ≠ 0 := by linarith
  have hp0' : p 0 = 1 - ρ := by
    calc p 0 = (1 - ρ) * ((1 - ρ)⁻¹ * p 0) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      _ = 1 - ρ := by rw [heq, mul_one]
  refine ⟨hlt, fun n => ?_⟩
  rw [hrec n, hp0']; ring

open QueueingFundamentals.BirthDeath in
theorem solution (lam mu ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hρ : ρ = lam / mu) :
    ((∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (fun _ => mu) p) ↔ ρ < 1) ∧
      (ρ < 1 → ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (fun _ => mu) p ↔
        ∀ n : ℕ, p n = (1 - ρ) * ρ ^ n) := by
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos hlam hmu
  refine ⟨⟨fun ⟨p, hp⟩ => (mm1ss_fwd lam mu ρ hmu hρ hρ0 p hp).1,
    fun h1 => ⟨_, mm1ss_geo lam mu ρ hmu hρ hρ0 h1⟩⟩, fun h1 p => ⟨fun hp =>
    (mm1ss_fwd lam mu ρ hmu hρ hρ0 p hp).2, fun h => ?_⟩⟩
  have : p = fun n => (1 - ρ) * ρ ^ n := funext h
  subst this
  exact mm1ss_geo lam mu ρ hmu hρ hρ0 h1
