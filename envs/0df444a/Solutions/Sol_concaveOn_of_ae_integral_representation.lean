-- Prove2me | solution 1 for concaveOn_of_ae_integral_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T00:16:39.145361+00:00
-- url     : https://prove2.me/submissions/fca539d0-a3d7-4094-ae0f-0b537c2894c0

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (F : ℝ → ℝ) (g : Y → ℝ → ℝ)
    (hF : ∀ x, 0 ≤ x → F x = ∫ y, g y x ∂μ)
    (hconcave : ∀ᵐ y ∂μ, ConcaveOn ℝ (Set.Ici 0) (g y))
    (hint : ∀ x, 0 ≤ x → Integrable (fun y => g y x) μ) :
    ConcaveOn ℝ (Set.Ici 0) F := by
  constructor
  · intro x hx y hy a b ha hb hab
    change 0 ≤ a * x + b * y
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  · intro x hx z hz u v hu hv huv
    let w : ℝ := u • x + v • z
    have hw : 0 ≤ w := by
      dsimp [w]
      exact add_nonneg (smul_nonneg hu hx) (smul_nonneg hv hz)
    have hFx := hint x hx
    have hFz := hint z hz
    have hFw := hint w hw
    have hUx : Integrable (fun y => u • g y x) μ := by
      simpa [smul_eq_mul, mul_comm] using hFx.const_mul u
    have hVz : Integrable (fun y => v • g y z) μ := by
      simpa [smul_eq_mul, mul_comm] using hFz.const_mul v
    have hPointwise : ∀ᵐ y ∂μ,
        u • g y x + v • g y z ≤ g y w := by
      filter_upwards [hconcave] with y hy
      exact hy.2 hx hz hu hv huv
    have hIntegral := integral_mono_ae (hUx.add hVz) hFw hPointwise
    calc
      u • F x + v • F z = ∫ y, u • g y x + v • g y z ∂μ := by
        rw [integral_add hUx hVz, integral_smul, integral_smul,
          hF x hx, hF z hz]
      _ ≤ ∫ y, g y w ∂μ := hIntegral
      _ = F w := (hF w hw).symm
