-- Prove2me | solution 1 for ShorNonsmooth.Stochastic.conditional_one_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:14:23.182995+00:00
-- url     : https://prove2.me/submissions/105df217-6f7c-4b38-8dcb-6fdf1f06eb3e

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_stochIter_measurable_of_stronglyMeasurable
import Theorems.Thm_stochIter_sq_integrable
import Theorems.Thm_condExp_add_lam_g
import Theorems.Thm_condExp_sub_lam_g
import Theorems.Thm_condExp_mul_lam_g
import Theorems.Thm_conditional_one_step_expansion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : xstar ∈ ShorNonsmooth.SubgradMethod.MinSet f)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j)) (k : ℕ)
    (hG_int : Integrable (G k) μ)
    (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hG_mean : ∀ᵐ ω ∂μ, ShorNonsmooth.AlmostDiff.IsSubgradient f (stochIter h G x₀ k ω) ((μ[G k | ℱ k]) ω))
    (hG_sq : ∀ᵐ ω ∂μ, (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω ≤ c)
    (B : ℝ) (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ) :
    Integrable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ ∧
      μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k] ≤ᵐ[μ]
        fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 + c * h k (stochIter h G x₀ k ω) ^ 2 := by
  have hFil_le : (ℱ k : MeasurableSpace Ω) ≤ m0 := ℱ.le k
  -- `x_k` is `ℱ k`-measurable, hence so is `x_k - x*`.
  have hxk_meas : Measurable[(ℱ k : MeasurableSpace Ω)] (stochIter h G x₀ k) :=
    stochIter_measurable_of_stronglyMeasurable ℱ h hh_meas G x₀ hG_meas k
  have hdx : Measurable[(ℱ k : MeasurableSpace Ω)]
      (fun ω => stochIter h G x₀ k ω - xstar) :=
    hxk_meas.sub measurable_const
  -- `x_k - x*` is `ℱ k`-measurable, hence `ℱ k`-a.e. strongly measurable.
  have hdx_ae : AEStronglyMeasurable[(ℱ k : MeasurableSpace Ω)]
      (fun ω => stochIter h G x₀ k ω - xstar) μ :=
    hdx.aestronglyMeasurable
  -- `ℱ k ≤ m0`, so the same function is `m0`-measurable, hence `m0`-a.e. strongly
  -- measurable.  The `m0`-level hypothesis is the one that pairs with `G k` in the
  -- inner product: `AEStronglyMeasurable.inner` needs both factors in the *same*
  -- measurable space.
  have hdx_m0 : Measurable[m0] (fun ω => stochIter h G x₀ k ω - xstar) := by
    refine Measurable.mono hdx hFil_le ?_
    exact @le_refl (MeasurableSpace (EuclideanSpace ℝ (Fin n)))
      (MeasurableSpace.instPartialOrder (α := EuclideanSpace ℝ (Fin n))).toPreorder _
  have hdx_ae_m0 : AEStronglyMeasurable
      (fun ω => stochIter h G x₀ k ω - xstar) μ :=
    Measurable.aestronglyMeasurable hdx_m0
  have hGk_ae_m0 : AEStronglyMeasurable (G k) μ := hG_int.aestronglyMeasurable
  -- The integrability of the cross term `⟪x_k - x*, G k ω⟫`.
  have hinter : Integrable (fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ := by
    have hinter_ae : AEStronglyMeasurable
        (fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ :=
      hdx_ae_m0.inner hGk_ae_m0
    -- `x_k - x*` and `G k` are both in `L^2`, so their norms are in `L^2` as well.
    have hu2 : MemLp (fun ω => stochIter h G x₀ k ω - xstar) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hdx_ae_m0).mpr hx_int
    have hG2 : MemLp (fun ω => G k ω) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hGk_ae_m0).mpr hG_sq_int
    -- Hölder: `‖x_k - x*‖ * ‖G k‖` is in `L^1`.
    have hbound_int : Integrable
        (fun ω => ‖stochIter h G x₀ k ω - xstar‖ * ‖G k ω‖) μ := by
      have hmul : MemLp (fun ω => ‖stochIter h G x₀ k ω - xstar‖ * ‖G k ω‖) 1 μ :=
        hG2.norm.mul' hu2.norm (r := 1)
      exact memLp_one_iff_integrable.mp hmul
    -- Cauchy–Schwarz bounds the inner product by that product.
    refine Integrable.mono hbound_int hinter_ae ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact abs_real_inner_le_norm _ _
  -- The pull-out of the inner product: only the LEFT factor must be `ℱ k`-measurable.
  have hinner_pull : μ[fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ | ℱ k]
      =ᵐ[μ] fun ω => ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ := by
    have hbil := condExp_bilin_of_aestronglyMeasurable_left
      (m := (ℱ k : MeasurableSpace Ω)) (mΩ := m0)
      (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin n)) (G := ℝ)
      (isBoundedBilinearMap_inner.toContinuousLinearMap)
      hdx_ae hinter hG_int
    filter_upwards [hbil] with ω hω; exact hω
  -- The one-step conditional expansion.
  have hce : μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k]
      =ᵐ[μ] fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2
        - 2 * (h k (stochIter h G x₀ k ω)
            * ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ)
        + (h k (stochIter h G x₀ k ω)) ^ 2
          * (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω :=
    conditional_one_step_expansion μ ℱ h hh_meas G x₀ k xstar B hh_pos hh_bdd
      hG_sq_int hx_int hG_meas hFil_le hdx hinter hinner_pull
  -- The cross term is nonneg: the conditional mean is a subgradient at `x_k`.
  have hsub_ineq : ∀ᵐ ω ∂μ,
      ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ
        ≥ f (stochIter h G x₀ k ω) - f xstar := by
    filter_upwards [hG_mean] with ω hω
    have h1 := hω xstar
    have h2 := hmin (stochIter h G x₀ k ω)
    -- `h1 : ⟪g, xstar - x_k⟫_ℝ ≤ f xstar - f x_k`
    -- By bilinearity and symmetry of the real inner product:
    -- `⟪x_k - xstar, g⟫_ℝ = -⟪g, xstar - x_k⟫_ℝ`.
    have h3 : ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ
        = -⟪(μ[G k | ℱ k]) ω, xstar - stochIter h G x₀ k ω⟫_ℝ := by
      simp only [inner_sub_left, inner_sub_right]
      simp only [real_inner_comm]
      ring
    linarith
  -- The integrability of the next iterate's squared distance.
  have hnext_int : Integrable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ :=
    stochIter_sq_integrable μ ℱ h hh_meas G x₀ xstar k B hh_pos hh_bdd
      hG_int hG_sq_int hx_int hxk_meas
  have hbound_ae : μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k]
      ≤ᵐ[μ] fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 + c * h k (stochIter h G x₀ k ω) ^ 2 := by
    filter_upwards [hce, hG_sq, hsub_ineq] with ω hω1 hω2 hω3
    rw [hω1]
    have hsqbound : (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω ≤ c := hω2
    have hsub := hω3
    have hpos : 0 < h k (stochIter h G x₀ k ω) := hh_pos _
    -- `xstar` is a minimiser, so `f xstar ≤ f x_k`; together with the subgradient
    -- inequality this makes the cross term nonnegative.
    have hmin' : f xstar ≤ f (stochIter h G x₀ k ω) := hmin (stochIter h G x₀ k ω)
    have hcross : 0 ≤ ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ := by linarith
    nlinarith [mul_nonneg (le_of_lt hpos) (le_of_lt hpos),
      mul_nonneg hcross (le_of_lt hpos)]
  exact ⟨hnext_int, hbound_ae⟩
