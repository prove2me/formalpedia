-- Prove2me | solution 1 for PolyakJuditsky.Averaging.step_size_mul_t_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:15:46.618992+00:00
-- url     : https://prove2.me/submissions/922fcaa2-5267-4af4-9685-79ff70dc25de

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

theorem aux_sst_step (γ : ℕ → ℝ) (δ : ℝ) (hδpos : 0 < δ) (hδle : δ ≤ 1 / 2)
    (t : ℕ) (g0 : 0 < γ t) (g1 : 0 < γ (t + 1)) (hle1 : γ t ≤ 1)
    (hb : ‖(γ t - γ (t + 1)) / γ t‖ ≤ δ * ‖γ t‖) :
    1 / γ (t + 1) ≤ 1 / γ t + 2 * δ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos g0,
    div_le_iff₀ g0] at hb
  have hd := le_abs_self (γ t - γ (t + 1))
  have e1 : δ * γ t ≤ 1 / 2 := by nlinarith
  have e2 : γ t - γ (t + 1) ≤ δ * γ t * γ t := by linarith
  have e3 : δ * γ t * γ t ≤ γ t / 2 := by nlinarith
  have e4 : γ t / 2 ≤ γ (t + 1) := by linarith
  have e5 : δ * γ t * γ t ≤ 2 * δ * γ t * γ (t + 1) := by
    have : 0 < δ * γ t := by positivity
    nlinarith
  have key : γ t ≤ (1 + 2 * δ * γ t) * γ (t + 1) := by nlinarith
  have : 1 / γ t + 2 * δ = (1 + 2 * δ * γ t) / γ t := by
    field_simp
  rw [this, div_le_div_iff₀ g1 g0]
  linarith

end PolyakJuditsky.Averaging

open PolyakJuditsky.Averaging
open Filter Topology

theorem solution (γ : ℕ → ℝ) (hγ : StepCondition4 γ) :
    Tendsto (fun t : ℕ => (t : ℝ) * γ t) atTop atTop := by
  obtain ⟨hpos, hlim, hlo⟩ := hγ
  rw [tendsto_atTop]
  intro M0
  set M : ℝ := max M0 1 with hM
  have hM0 : M0 ≤ M := le_max_left _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  set δ : ℝ := 1 / (4 * M) with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; linarith
  have h1 := hlo.bound hδpos
  have h2 : ∀ᶠ t in atTop, γ t ≤ 1 := hlim.eventually (ge_mem_nhds one_pos)
  have h3 : ∀ᶠ t : ℕ in atTop, 1 ≤ t := eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  have step : ∀ t, T ≤ t → 1 / γ (t + 1) ≤ 1 / γ t + 2 * δ := by
    intro t ht
    obtain ⟨hb, hle1, ht1⟩ := hT t ht
    exact aux_sst_step γ δ hδpos hδle t (hpos t ht1) (hpos (t + 1) (by omega)) hle1 hb
  have iter : ∀ n : ℕ, 1 / γ (T + n) ≤ 1 / γ T + 2 * δ * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step (T + n) (by omega)
      push_cast
      rw [← add_assoc]
      linarith
  have hT1 : 1 ≤ T := (hT T le_rfl).2.2
  have gT : 0 < γ T := hpos T hT1
  rw [eventually_atTop]
  refine ⟨T + ⌈2 * M * (1 / γ T)⌉₊, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = T + n := ⟨t - T, by omega⟩
  have hn : ⌈2 * M * (1 / γ T)⌉₊ ≤ n := by omega
  have hn' : 2 * M * (1 / γ T) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have gt : 0 < γ (T + n) := hpos (T + n) (by omega)
  have hit := iter n
  have hMd : M * (2 * δ * n) = n / 2 := by
    rw [hδ]; field_simp; ring
  have hbound : M * (1 / γ (T + n)) ≤ ((T + n : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hit hMpos.le
    push_cast
    have hTnn : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have : M ≤ ((T + n : ℕ) : ℝ) * γ (T + n) := by
    have := mul_le_mul_of_nonneg_right hbound gt.le
    rw [mul_assoc, one_div, inv_mul_cancel₀ gt.ne', mul_one] at this
    exact this
  linarith
