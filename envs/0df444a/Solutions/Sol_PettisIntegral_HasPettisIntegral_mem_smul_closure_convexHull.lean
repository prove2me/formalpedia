-- Prove2me | solution 1 for PettisIntegral.HasPettisIntegral.mem_smul_closure_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:03:52.89087+00:00
-- url     : https://prove2.me/submissions/885cf463-2ee5-4680-ad5c-4ec1db5f7cd2

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

open PettisIntegral

theorem solution {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] {μ : Measure X} [IsFiniteMeasure μ] [μ.Regular] {f : X → E} (hf : Continuous f)
    {a : E} (ha : HasPettisIntegral 𝕜 μ f a) :
    a ∈ (μ Set.univ).toReal • closure (convexHull ℝ (Set.range f)) := by
  have _ := hf
  -- the topology of `E` is locally convex for the underlying real structure
  have hsmul : ContinuousSMul ℝ E := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  have hLC : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  have hKconv : Convex ℝ (closure (convexHull ℝ (Set.range f))) :=
    (convex_convexHull ℝ (Set.range f)).closure
  have hKclosed : IsClosed (closure (convexHull ℝ (Set.range f))) := isClosed_closure
  have hfK : ∀ x, f x ∈ closure (convexHull ℝ (Set.range f)) := fun x =>
    subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x))
  by_cases hμ : μ = 0
  · -- the zero measure: the integral is `0`
    have ha0 : a = 0 := by
      by_contra hne
      obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hne
      have h1 : φ a = 0 := by
        rw [ha.2 φ, hμ]
        exact integral_zero_measure _
      rw [h1, map_zero φ] at hφ
      exact lt_irrefl _ hφ
    have h0 : (μ Set.univ).toReal = 0 := by
      rw [hμ]
      simp
    rw [h0, Set.zero_smul_set ⟨f (Classical.arbitrary X), hfK _⟩, ha0]
    exact Set.mem_zero.mpr rfl
  · have hc : 0 < (μ Set.univ).toReal :=
      ENNReal.toReal_pos (by simpa using hμ) (measure_ne_top μ _)
    have hb : (μ Set.univ).toReal⁻¹ • a ∈ closure (convexHull ℝ (Set.range f)) := by
      by_contra hb
      -- separate the point from the closed convex set by a continuous linear form
      obtain ⟨φ, u, hφb, hφK⟩ :=
        RCLike.geometric_hahn_banach_point_closed (𝕜 := 𝕜) hKconv hKclosed hb
      have hint : Integrable (fun x => φ (f x)) μ := ha.1 φ
      have h1 : RCLike.re (φ a) = ∫ x, RCLike.re (φ (f x)) ∂μ := by
        rw [ha.2 φ]
        exact (integral_re hint).symm
      have h2 : (μ Set.univ).toReal * u ≤ ∫ x, RCLike.re (φ (f x)) ∂μ := by
        have h := integral_mono (μ := μ) (integrable_const u) hint.re
          (fun x => (hφK _ (hfK x)).le)
        rw [integral_const, smul_eq_mul] at h
        exact h
      have h3 : RCLike.re (φ ((μ Set.univ).toReal⁻¹ • a))
          = (μ Set.univ).toReal⁻¹ * RCLike.re (φ a) := by
        rw [ContinuousLinearMap.map_smul_of_tower φ ((μ Set.univ).toReal⁻¹) a, RCLike.smul_re]
      rw [h3, h1] at hφb
      have h4 : (μ Set.univ).toReal⁻¹ * ((μ Set.univ).toReal * u)
          ≤ (μ Set.univ).toReal⁻¹ * ∫ x, RCLike.re (φ (f x)) ∂μ :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hc.le)
      rw [inv_mul_cancel_left₀ hc.ne'] at h4
      exact absurd hφb (not_lt.mpr h4)
    refine ⟨(μ Set.univ).toReal⁻¹ • a, hb, ?_⟩
    show (μ Set.univ).toReal • ((μ Set.univ).toReal⁻¹ • a) = a
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
