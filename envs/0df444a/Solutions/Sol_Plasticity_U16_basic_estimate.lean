-- Prove2me | solution 1 for Plasticity.U16.basic_estimate
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:07:07.934821+00:00
-- url     : https://prove2.me/submissions/4e2f388c-6854-478e-b307-b2dca910676e

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Plasticity_U16_norm_eq

namespace Sol_Plasticity_U16_basic_estimate

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

/-- A functional of norm at most one is bounded by the norm. -/
lemma dual_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (ψ : StrongDual ℝ Y)
    (hψ : ‖ψ‖ ≤ 1) (v : Y) : ψ v ≤ ‖v‖ := by
  have h1 := ψ.le_opNorm v
  have h2 : ‖ψ‖ * ‖v‖ ≤ ‖v‖ := by
    have := mul_le_mul_of_nonneg_right hψ (norm_nonneg v)
    simpa using this
  have h3 : ψ v ≤ ‖ψ v‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  linarith

end Sol_Plasticity_U16_basic_estimate

open Sol_Plasticity_U16_basic_estimate in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → X)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, x i ∈ Metric.closedBall (0 : X) 1)
    (hD : ∑ i ∈ s, c i • F (x i) ≠ 0)
    (a : X) (ha : a ∈ Metric.closedBall (0 : X) 1)
    (hFa : F a = -(‖∑ i ∈ s, c i • F (x i)‖⁻¹ • ∑ i ∈ s, c i • F (x i)))
    (b : X) (hb : b ∈ Metric.closedBall (0 : X) 1) (hba : ‖b - a‖ ≤ 1 / 4) :
    ‖∑ i ∈ s, c i • F (x i)‖ / 2 ≤ ∑ i ∈ s, c i * ‖b - x i‖ - (∑ i ∈ s, c i) * ‖b‖ := by
  set D : Y := ∑ i ∈ s, c i • F (x i) with hDdef
  have hDn : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  -- The child card: `F` preserves norms on the ball.
  have hN := (Plasticity.U16.norm_eq F hmaps hlip hsphere hcover).2
  -- `F a` is the unit vector opposite to `D`, so `‖a‖ = 1`.
  have hFa1 : ‖F a‖ = 1 := by
    rw [hFa, norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hDn]
  have ha1 : ‖a‖ = 1 := by rw [← hN a ha, hFa1]
  have hFb : ‖F b‖ = ‖b‖ := hN b hb
  have hab : ‖a‖ - ‖b‖ ≤ ‖b - a‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le a b
  -- A norming functional at `F b`.
  obtain ⟨ψ, hψ1, hψb⟩ := exists_dual_vector'' ℝ (F b)
  have hψb' : ψ (F b) = ‖b‖ := by rw [hψb, hFb]; rfl
  -- `ψ (F a) ≥ 1/2`.
  have hψa : 1 / 2 ≤ ψ (F a) := by
    have h1 := dual_le ψ hψ1 (F b - F a)
    have h2 := lip_norm hlip hb ha
    rw [map_sub] at h1
    linarith
  -- `ψ (F (x i)) ≥ ‖b‖ - ‖b - x i‖`.
  have hψx : ∀ i ∈ s, ‖b‖ - ‖b - x i‖ ≤ ψ (F (x i)) := by
    intro i hi
    have h1 := dual_le ψ hψ1 (F b - F (x i))
    have h2 := lip_norm hlip hb (hx i hi)
    rw [map_sub] at h1
    linarith
  -- `D = -‖D‖ • F a`, hence `ψ D = -‖D‖ * ψ (F a)`.
  have hDa : D = -‖D‖ • F a := by
    rw [hFa, smul_neg, neg_smul, neg_neg, smul_smul, mul_inv_cancel₀ hDn, one_smul]
  have hψD : ψ D = -‖D‖ * ψ (F a) := by
    rw [← smul_eq_mul, ← map_smul, ← hDa]
  -- `ψ D` as a sum.
  have hψsum : ψ D = ∑ i ∈ s, c i * ψ (F (x i)) := by
    rw [hDdef, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hlow : ∑ i ∈ s, c i * (‖b‖ - ‖b - x i‖) ≤ ∑ i ∈ s, c i * ψ (F (x i)) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hψx i hi) (hc i hi)
  have hexp : ∑ i ∈ s, c i * (‖b‖ - ‖b - x i‖)
      = (∑ i ∈ s, c i) * ‖b‖ - ∑ i ∈ s, c i * ‖b - x i‖ := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmain : ‖D‖ / 2 ≤ ‖D‖ * ψ (F a) := by
    have := mul_le_mul_of_nonneg_left hψa hDpos.le
    linarith
  linarith
