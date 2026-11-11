-- Prove2me | solution 1 for StochModelWC.StrongCvx.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:06:17.133748+00:00
-- url     : https://prove2.me/submissions/200d19f4-a66c-4da3-b933-3eeef3583073

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Tactic.Ring
import Definitions.Def_StochModelWC_ModelBased_AssumptionB
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

-- Source component: P094_measurability

open MeasureTheory

noncomputable section
namespace Prove2MeS03

attribute [local instance] Classical.propDecidable

/-- A real-valued function whose restricted epigraph is closed has a Borel domain
and a measurable extension by zero. No regularity outside the domain is needed. -/
theorem closed_epigraph_measurable
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (D : Set X) (r : X → ℝ)
    (hr : IsClosed {p : X × ℝ | p.1 ∈ D ∧ r p.1 ≤ p.2}) :
    MeasurableSet D ∧ Measurable (fun x => if x ∈ D then r x else 0) := by
  classical
  have hsub (t : ℝ) : IsClosed {x : X | x ∈ D ∧ r x ≤ t} := by
    exact hr.preimage (continuous_id.prodMk continuous_const)
  have hdomain : D = ⋃ n : ℕ, {x : X | x ∈ D ∧ r x ≤ (n : ℝ)} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (r x)
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  have hD : MeasurableSet D := by
    rw [hdomain]
    exact MeasurableSet.iUnion (fun n => (hsub (n : ℝ)).measurableSet)
  refine ⟨hD, measurable_of_Iic (fun t => ?_)⟩
  change MeasurableSet {x : X | (if x ∈ D then r x else 0) ≤ t}
  by_cases ht : 0 ≤ t
  · have he : {x : X | (if x ∈ D then r x else 0) ≤ t} =
        {x : X | x ∈ D ∧ r x ≤ t} ∪ Dᶜ := by
      ext x
      by_cases hx : x ∈ D <;> simp [hx, ht]
    rw [he]
    exact (hsub t).measurableSet.union hD.compl
  · have he : {x : X | (if x ∈ D then r x else 0) ≤ t} =
        {x : X | x ∈ D ∧ r x ≤ t} := by
      ext x
      by_cases hx : x ∈ D <;> simp [hx, ht]
    rw [he]
    exact (hsub t).measurableSet

/-- Every measurable map into the effective domain sees measurable values. -/
theorem closed_epigraph_measurable_comp
    {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ω] (D : Set X) (r : X → ℝ)
    (hr : IsClosed {p : X × ℝ | p.1 ∈ D ∧ r p.1 ≤ p.2})
    (g : Ω → X) (hg : Measurable g) (hmem : ∀ ω, g ω ∈ D) :
    Measurable (fun ω => r (g ω)) := by
  classical
  have h := (closed_epigraph_measurable D r hr).2.comp hg
  simpa only [Function.comp_def, if_pos (hmem _)] using h

end Prove2MeS03

-- Source component: P094_moment_lipschitz

open MeasureTheory

namespace Prove2MeS03

/-- A nonnegative random Lipschitz coefficient with the prescribed square-moment
bound is integrable, and its first moment is at most that same bound. -/
theorem first_moment_of_square_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → ℝ) (hqmeas : Measurable q) (hq0 : ∀ ξ, 0 ≤ q ξ)
    (hqsq : Integrable (fun ξ => q ξ ^ 2) P) (L : ℝ)
    (hL : Real.sqrt (∫ ξ, q ξ ^ 2 ∂P) ≤ L) :
    0 ≤ L ∧ Integrable q P ∧ (∫ ξ, q ξ ∂P) ≤ L ∧
      (∫ ξ, q ξ ^ 2 ∂P) ≤ L ^ 2 := by
  have hL0 : 0 ≤ L := (Real.sqrt_nonneg _).trans hL
  have hq : Integrable q P := by
    apply ((integrable_const (1 : ℝ)).add hqsq).mono_nonneg hqmeas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hq0
    · exact Filter.Eventually.of_forall (fun ξ => by
        change q ξ ≤ 1 + q ξ ^ 2
        nlinarith [sq_nonneg (q ξ - 1 / 2)])
  have hs0 : 0 ≤ ∫ ξ, q ξ ^ 2 ∂P := integral_nonneg (fun ξ => sq_nonneg (q ξ))
  have hsqrt := Real.sq_sqrt hs0
  have hsL : (∫ ξ, q ξ ^ 2 ∂P) ≤ L ^ 2 := by
    nlinarith [Real.sqrt_nonneg (∫ ξ, q ξ ^ 2 ∂P)]
  let a : ℝ := ∫ ξ, q ξ ∂P
  have ha0 : 0 ≤ a := integral_nonneg hq0
  have hcomp : (∫ ξ, (2 * a) * q ξ ∂P) ≤
      ∫ ξ, q ξ ^ 2 + a ^ 2 ∂P := by
    apply integral_mono (hq.const_mul (2 * a)) (hqsq.add (integrable_const (a ^ 2)))
    intro ξ
    change (2 * a) * q ξ ≤ q ξ ^ 2 + a ^ 2
    nlinarith [sq_nonneg (q ξ - a)]
  rw [integral_const_mul, integral_add hqsq (integrable_const (a ^ 2))] at hcomp
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hcomp
  have haL : a ≤ L := by
    change (2 * a) * a ≤ (∫ ξ, q ξ ^ 2 ∂P) + a ^ 2 at hcomp
    nlinarith
  exact ⟨hL0, hq, haL, hsL⟩


/-- Expected touching and one-sided accuracy turn the random one-sided model
bound into the deterministic Lipschitz bound used in the descent estimate. -/
theorem lipschitz_from_model
    {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Set E)
    (f : E → ℝ) (model : E → E → Ω → ℝ)
    (q : Ω → ℝ) (L : ℝ) (hq : Integrable q P) (hmean : (∫ ξ, q ξ ∂P) ≤ L)
    (hint : ∀ x ∈ U, ∀ y ∈ U, Integrable (fun ξ => model x y ξ) P)
    (htouch : ∀ x ∈ U, (∫ ξ, model x x ξ ∂P) = f x)
    (haccuracy : ∀ x ∈ U, ∀ y ∈ U, (∫ ξ, model x y ξ - f y ∂P) ≤ 0)
    (hmodel : ∀ x ∈ U, ∀ᵐ ξ ∂P, ∀ y ∈ U,
      model x x ξ - model x y ξ ≤ q ξ * ‖x - y‖) :
    ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ L * ‖x - y‖ := by
  have hone (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) :
      f x - f y ≤ L * ‖x - y‖ := by
    have hm := integral_mono_ae ((hint x hx x hx).sub (hint x hx y hy))
      (hq.mul_const ‖x - y‖) ((hmodel x hx).mono (fun ξ h => h y hy))
    change (∫ ξ, model x x ξ - model x y ξ ∂P) ≤
      ∫ ξ, q ξ * ‖x - y‖ ∂P at hm
    rw [integral_sub (hint x hx x hx) (hint x hx y hy), htouch x hx,
      integral_mul_const] at hm
    have ha := haccuracy x hx y hy
    rw [integral_sub (hint x hx y hy) (integrable_const (f y))] at ha
    simp only [integral_const, probReal_univ, one_smul] at ha
    have hc := mul_le_mul_of_nonneg_right hmean (norm_nonneg (x - y))
    linarith
  intro x hx y hy
  refine abs_le.mpr ⟨?_, hone x hx y hy⟩
  have h := hone y hy x hx
  rw [norm_sub_rev] at h
  linarith

end Prove2MeS03

-- Source component: P094_fiber_transfer

open MeasureTheory

namespace Prove2MeS03

/-- A nonnegative one-step observable transfers to an independent random base
using only the integrable bound on its fibre expectations. No model value at
a random base is assumed integrable. -/
theorem nonnegative_fiber_transfer
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (F : A × B → ℝ) (hF : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hfiber : ∀ x, Integrable (fun y => F (x, y)) ν)
    (G : A → ℝ) (hG : Integrable G μ)
    (hbound : ∀ x, (∫ y, F (x, y) ∂ν) ≤ G x) :
    Integrable F (μ.prod ν) ∧
      (∫ p, F p ∂(μ.prod ν)) ≤ ∫ x, G x ∂μ := by
  have hinner : Integrable (fun x => ∫ y, F (x, y) ∂ν) μ := by
    apply hG.mono_nonneg
      hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => integral_nonneg (fun y => hF0 (x, y)))
    · exact Filter.Eventually.of_forall hbound
  have hnorm : (fun x => ∫ y, ‖F (x, y)‖ ∂ν) =
      (fun x => ∫ y, F (x, y) ∂ν) := by
    funext x
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hF0 (x, y)))
  have hprod : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall hfiber, ?_⟩
    rw [hnorm]
    exact hinner
  refine ⟨hprod, ?_⟩
  rw [integral_prod F hprod]
  exact integral_mono hinner hG hbound

end Prove2MeS03

-- Source component: P094_one_step

open Filter Topology
open MeasureTheory

namespace Prove2MeS03.P094

/-- A minimizer of a strongly convex function has the full quadratic growth bound. -/
theorem strong_min_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} {g : E → ℝ} {κ : ℝ} (hg : StrongConvexOn D κ g)
    {v z : E} (hv : v ∈ D) (hz : z ∈ D) (hmin : IsMinOn g D v) :
    g v + κ / 2 * ‖v - z‖ ^ 2 ≤ g z := by
  have hstep (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      (1 - t) * (κ / 2 * ‖v - z‖ ^ 2) ≤ g z - g v := by
    have hsum : (1 - t) + t = 1 := by ring
    have hmem := hg.1 hv hz (show 0 ≤ 1 - t by linarith) ht.le hsum
    have hconv := hg.2 hv hz (show 0 ≤ 1 - t by linarith) ht.le hsum
    have hm := hmin hmem
    change g v ≤ g ((1 - t) • v + t • z) at hm
    simp only [smul_eq_mul] at hconv
    have hscaled : t * ((1 - t) * (κ / 2 * ‖v - z‖ ^ 2)) ≤
        t * (g z - g v) := by nlinarith
    nlinarith
  have hlim : Tendsto (fun t : ℝ => (1 - t) * (κ / 2 * ‖v - z‖ ^ 2))
      (𝓝[>] 0) (𝓝 (κ / 2 * ‖v - z‖ ^ 2)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) * (κ / 2 * ‖v - z‖ ^ 2)) :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hgrowth : κ / 2 * ‖v - z‖ ^ 2 ≤ g z - g v := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hstep t ht.1 ht.2
  linarith


/-- Adding a centered quadratic adds its curvature to the strong-convexity modulus. -/
theorem regularized_strong_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {D : Set E} {g : E → ℝ} {κ β : ℝ}
    (hg : StrongConvexOn D κ g) (x : E) :
    StrongConvexOn D (κ + β) (fun y => g y + β / 2 * ‖y - x‖ ^ 2) := by
  rw [strongConvexOn_iff_convex] at hg ⊢
  have hlin : ConvexOn ℝ D
      (fun y : E => β / 2 * ‖x‖ ^ 2 - β * inner ℝ y x) := by
    refine ⟨hg.1, ?_⟩
    intro y hy z hz a b ha hb hab
    simp only [smul_eq_mul, inner_add_left, real_inner_smul_left]
    apply le_of_eq
    calc
      β / 2 * ‖x‖ ^ 2 - β * (a * inner ℝ y x + b * inner ℝ z x) =
          (a + b) * (β / 2 * ‖x‖ ^ 2) -
            β * (a * inner ℝ y x + b * inner ℝ z x) := by rw [hab]; ring
      _ = a * (β / 2 * ‖x‖ ^ 2 - β * inner ℝ y x) +
          b * (β / 2 * ‖x‖ ^ 2 - β * inner ℝ z x) := by ring
  have heq : (fun y => g y + β / 2 * ‖y - x‖ ^ 2 - (κ + β) / 2 * ‖y‖ ^ 2) =
      ((fun y => g y - κ / 2 * ‖y‖ ^ 2) +
        (fun y => β / 2 * ‖x‖ ^ 2 - β * inner ℝ y x)) := by
    funext y
    simp only [Pi.add_apply, norm_sub_sq_real]
    ring
  rw [heq]
  exact hg.add hlin

/-- The deterministic three-point bound for a strongly convex proximal model. -/
theorem regularized_min_three_point {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {D : Set E} {g : E → ℝ} {κ β : ℝ}
    (hg : StrongConvexOn D κ g) (x : E) {v z : E}
    (hv : v ∈ D) (hz : z ∈ D)
    (hmin : IsMinOn (fun y => g y + β / 2 * ‖y - x‖ ^ 2) D v) :
    g v + β / 2 * ‖v - x‖ ^ 2 + (κ + β) / 2 * ‖v - z‖ ^ 2 ≤
      g z + β / 2 * ‖z - x‖ ^ 2 :=
  strong_min_growth (regularized_strong_convex hg x) hv hz hmin


/-- Completing the square in the stochastic Lipschitz error. -/
theorem quadratic_error_bound (a d β : ℝ) (hβ : 0 < β) :
    a * d - β / 2 * d ^ 2 ≤ a ^ 2 / (2 * β) := by
  apply (le_div_iff₀ (show 0 < 2 * β by positivity)).mpr
  nlinarith [sq_nonneg (β * d - a)]

/-- Pathwise one-step domination; its right side uses only fixed model sections. -/
theorem one_step_pathwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : Set E} (f r model : E → ℝ) (x v z : E) (μ β K ℓ : ℝ)
    (hβ : 0 < β) (hv : v ∈ D) (hz : z ∈ D)
    (hconv : StrongConvexOn D μ (fun y => model y + r y))
    (hmin : IsMinOn (fun y => r y + model y + β / 2 * ‖y - x‖ ^ 2) D v)
    (hf : f v - f x ≤ K * ‖v - x‖)
    (hmodel : model x - model v ≤ ℓ * ‖x - v‖) :
    (f v + r v - (f z + r z)) + (β + μ) / 2 * ‖v - z‖ ^ 2 ≤
      β / 2 * ‖x - z‖ ^ 2 + (K + ℓ) ^ 2 / (2 * β) +
        (model z - f z) + (f x - model x) := by
  have hm : IsMinOn (fun y => (model y + r y) + β / 2 * ‖y - x‖ ^ 2) D v := by
    simpa only [add_comm (model _) (r _)] using hmin
  have hthree := regularized_min_three_point hconv x hv hz hm
  have hquad := quadratic_error_bound (K + ℓ) ‖v - x‖ β hβ
  rw [norm_sub_rev x v] at hmodel
  rw [norm_sub_rev z x] at hthree
  nlinarith


/-- Separate two nonnegative quantities under an integrable upper bound. -/
theorem integrable_nonneg_parts {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B R : Ω → ℝ} (hR : Integrable R P)
    (hA : AEStronglyMeasurable A P) (hB : AEStronglyMeasurable B P)
    (hA0 : ∀ ξ, 0 ≤ A ξ) (hB0 : ∀ ξ, 0 ≤ B ξ)
    (c : ℝ) (hc : 0 < c) (hbound : ∀ᵐ ξ ∂P, A ξ + c * B ξ ≤ R ξ) :
    Integrable A P ∧ Integrable B P := by
  have hAi : Integrable A P := hR.mono_nonneg hA (Eventually.of_forall hA0) (by
    filter_upwards [hbound] with ξ hξ
    nlinarith [hB0 ξ])
  have hBi : Integrable (fun ξ => c * B ξ) P :=
    hR.mono_nonneg (hB.const_mul c)
      (Eventually.of_forall fun ξ => mul_nonneg hc.le (hB0 ξ)) (by
        filter_upwards [hbound] with ξ hξ
        linarith [hA0 ξ])
  refine ⟨hAi, ?_⟩
  have hi := hBi.const_mul c⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hi

/-- Integrate the domination estimate without presupposing integrability on its left. -/
theorem expected_bound_of_pathwise {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B Q M N : Ω → ℝ)
    (C L β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (hA : AEStronglyMeasurable A P) (hB : AEStronglyMeasurable B P)
    (hA0 : ∀ ξ, 0 ≤ A ξ) (hB0 : ∀ ξ, 0 ≤ B ξ)
    (hQ : Integrable Q P) (hM : Integrable M P) (hN : Integrable N P)
    (hQmean : ∫ ξ, Q ξ ∂P ≤ L ^ 2) (hMmean : ∫ ξ, M ξ ∂P ≤ 0)
    (hNmean : ∫ ξ, N ξ ∂P = 0)
    (hbound : ∀ᵐ ξ ∂P, A ξ + (β + μ) / 2 * B ξ ≤
      C + (L ^ 2 + Q ξ) / β + M ξ + N ξ) :
    Integrable A P ∧ Integrable B P ∧
      (∫ ξ, A ξ + (β + μ) / 2 * B ξ ∂P) ≤ C + 2 * L ^ 2 / β := by
  let R (ξ : Ω) : ℝ := C + (L ^ 2 + Q ξ) / β + M ξ + N ξ
  have hq : Integrable (fun ξ => (L ^ 2 + Q ξ) / β) P :=
    ((integrable_const (L ^ 2)).add hQ).div_const β
  have hCq : Integrable (fun ξ => C + (L ^ 2 + Q ξ) / β) P :=
    (integrable_const C).add hq
  have hCqM : Integrable (fun ξ => C + (L ^ 2 + Q ξ) / β + M ξ) P :=
    hCq.add hM
  have hR : Integrable R P := (((integrable_const C).add hq).add hM).add hN
  obtain ⟨hAi, hBi⟩ := integrable_nonneg_parts P hR hA hB hA0 hB0
    ((β + μ) / 2) (by positivity) hbound
  refine ⟨hAi, hBi, ?_⟩
  have hleft : Integrable (fun ξ => A ξ + (β + μ) / 2 * B ξ) P :=
    hAi.add (hBi.const_mul _)
  have hle := integral_mono_ae hleft hR hbound
  have hRvalue : (∫ ξ, R ξ ∂P) =
      C + (L ^ 2 + ∫ ξ, Q ξ ∂P) / β + (∫ ξ, M ξ ∂P) + (∫ ξ, N ξ ∂P) := by
    dsimp only [R]
    rw [integral_add hCqM hN,
      integral_add hCq hM,
      integral_add (integrable_const C) hq, integral_div,
      integral_add (integrable_const (L ^ 2)) hQ]
    simp
  rw [hRvalue, hNmean, add_zero] at hle
  have hdiv : (L ^ 2 + ∫ ξ, Q ξ ∂P) / β ≤ 2 * L ^ 2 / β := by
    apply (div_le_div_iff_of_pos_right hβ).mpr
    linarith
  linarith


/-- The complete deterministic-base expected inequality, including integrability. -/
theorem deterministic_one_step {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model 0 (-μ) L Lfun)
    (β : ℕ → ℝ)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : StochModelWC.ModelBased.IsAlg41Step P U D r model β upd)
    (t : ℕ) (hβ : 0 < β t) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ D)
    (hstar : ∀ y ∈ D, f z + r z ≤ f y + r y) :
    Integrable (fun ξ => f (upd t x ξ) + r (upd t x ξ)) P ∧
    Integrable (fun ξ => ‖upd t x ξ - z‖ ^ 2) P ∧
    (∫ ξ, (f (upd t x ξ) + r (upd t x ξ) - (f z + r z)) +
      (β t + μ) / 2 * ‖upd t x ξ - z‖ ^ 2 ∂P) ≤
      β t / 2 * ‖x - z‖ ^ 2 + 2 * L ^ 2 / β t := by
  rcases hB with ⟨hUopen, hUconv, hDU, hMj, hMint, htouch, hacc,
    hweak, hLmeas, hL0, hLsq, hLbound, hB4⟩
  rcases hupd with ⟨hupdD, hupdMeas, hupdMin⟩
  obtain ⟨hLnonneg, hLint, hLmean, hLsqmean⟩ :=
    Prove2MeS03.first_moment_of_square_bound P Lfun hLmeas hL0 hLsq L hLbound
  have hacc0 : ∀ a ∈ U, ∀ b ∈ U, (∫ ξ, model a b ξ - f b ∂P) ≤ 0 := by
    intro a ha b hb
    simpa only [zero_div, zero_mul] using hacc a ha b hb
  have hfLip := Prove2MeS03.lipschitz_from_model P U f model Lfun L hLint hLmean
    hMint htouch hacc0 hB4
  have hvm : Measurable (fun ξ => upd t x ξ) :=
    (hupdMeas t).comp (measurable_const.prodMk measurable_id)
  have hrvm : Measurable (fun ξ => r (upd t x ξ)) :=
    Prove2MeS03.closed_epigraph_measurable_comp D r hr (fun ξ => upd t x ξ)
      hvm (hupdD t x)
  have hfvm : Measurable (fun ξ => f (upd t x ξ)) := hf.continuous.measurable.comp hvm
  let A (ξ : Ω) := f (upd t x ξ) + r (upd t x ξ) - (f z + r z)
  let B (ξ : Ω) := ‖upd t x ξ - z‖ ^ 2
  let M (ξ : Ω) := model x z ξ - f z
  let N (ξ : Ω) := f x - model x x ξ
  have hAm : AEStronglyMeasurable A P :=
    ((hfvm.add hrvm).sub measurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B P :=
    ((hvm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ => sub_nonneg.mpr (hstar _ (hupdD t x ξ))
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun ξ => sq_nonneg _
  have hMi : Integrable M P := (hMint x hx z (hDU hz)).sub (integrable_const (f z))
  have hNi : Integrable N P := (integrable_const (f x)).sub (hMint x hx x hx)
  have hMm : (∫ ξ, M ξ ∂P) ≤ 0 := hacc0 x hx z (hDU hz)
  have hNm : (∫ ξ, N ξ ∂P) = 0 := by
    dsimp only [N]
    rw [integral_sub (integrable_const (f x)) (hMint x hx x hx), htouch x hx]
    simp
  have hbnd : ∀ᵐ ξ ∂P, A ξ + (β t + μ) / 2 * B ξ ≤
      β t / 2 * ‖x - z‖ ^ 2 + (L ^ 2 + Lfun ξ ^ 2) / β t + M ξ + N ξ := by
    filter_upwards [hweak x hx, hupdMin t x hx, hB4 x hx] with ξ hw hm hmod
    have hs : StrongConvexOn D μ (fun y => model x y ξ + r y) := by
      rw [strongConvexOn_iff_convex]
      simpa only [StochModelWC.ModelBased.IsWeaklyConvexOn, neg_div, neg_mul,
        sub_eq_add_neg] using hw
    have hfv : f (upd t x ξ) - f x ≤ L * ‖upd t x ξ - x‖ :=
      (le_abs_self _).trans (hfLip _ (hDU (hupdD t x ξ)) x hx)
    have hp := one_step_pathwise f r (fun y => model x y ξ) x (upd t x ξ) z μ
      (β t) L (Lfun ξ) hβ (hupdD t x ξ) hz hs hm hfv
      (hmod _ (hDU (hupdD t x ξ)))
    have hsq : (L + Lfun ξ) ^ 2 / (2 * β t) ≤ (L ^ 2 + Lfun ξ ^ 2) / β t := by
      apply (div_le_div_iff₀ (show 0 < 2 * β t by positivity) hβ).mpr
      nlinarith [mul_nonneg hβ.le (sq_nonneg (L - Lfun ξ))]
    dsimp only [A, B, M, N]
    linarith
  obtain ⟨hAi, hBi, hE⟩ := expected_bound_of_pathwise P A B (fun ξ => Lfun ξ ^ 2)
    M N (β t / 2 * ‖x - z‖ ^ 2) L (β t) μ hβ hμ hAm hBm hA0 hB0
    hLsq hMi hNi hLsqmean hMm hNm hbnd
  refine ⟨?_, hBi, hE⟩
  have hi : Integrable (fun ξ => A ξ + (f z + r z)) P :=
    hAi.add (integrable_const (f z + r z))
  simpa only [A, sub_add_cancel] using hi


end Prove2MeS03.P094

-- Source component: P094_run_transfer

open MeasureTheory Filter Topology
open StochModelWC.ModelBased

namespace Prove2MeS03.P094

theorem run_snoc_prefix {d N : ℕ} {Ω : Type*}
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (ω : Fin N → Ω) (ξ : Ω)
    (t : ℕ) (ht : t ≤ N) : run upd x0 (Fin.snoc ω ξ) t = run upd x0 ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hn : t < N := by omega
    have hn1 : t < N + 1 := by omega
    simp only [run, dif_pos hn, dif_pos hn1]
    rw [ih (by omega)]
    congr 1
    exact @Fin.snoc_castSucc N (fun _ => Ω) ξ ω ⟨t, hn⟩

theorem run_snoc_last {d N : ℕ} {Ω : Type*}
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (ω : Fin N → Ω) (ξ : Ω) :
    run upd x0 (Fin.snoc ω ξ) (N + 1) = upd N (run upd x0 ω N) ξ := by
  rw [run, dif_pos (Nat.lt_succ_self N), run_snoc_prefix upd x0 ω ξ N le_rfl]
  congr 1
  exact Fin.snoc_last _ _

def sampleSnoc {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) :
    ((Fin N → Ω) × Ω) ≃ᵐ (Fin (N + 1) → Ω) :=
  (MeasurableEquiv.prodComm : ((Fin N → Ω) × Ω) ≃ᵐ (Ω × (Fin N → Ω))).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Ω) (Fin.last N)).symm

@[simp] theorem sampleSnoc_apply {Ω : Type*} [MeasurableSpace Ω] (N : ℕ)
    (p : (Fin N → Ω) × Ω) : sampleSnoc N p = Fin.snoc p.1 p.2 := by
  simp [sampleSnoc, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_last', MeasurableEquiv.prodComm, Equiv.prodComm]

theorem sampleSnoc_preserving {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) :
    MeasurePreserving (sampleSnoc (Ω := Ω) N)
      ((Measure.pi fun _ : Fin N => P).prod P)
      (Measure.pi fun _ : Fin (N + 1) => P) := by
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => P) (Fin.last N)).symm.comp
    Measure.measurePreserving_swap

theorem pi_snoc_integrable_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (F : (Fin (N + 1) → Ω) → ℝ) :
    Integrable F (Measure.pi fun _ : Fin (N + 1) => P) ↔
      Integrable (fun p : (Fin N → Ω) × Ω => F (Fin.snoc p.1 p.2))
        ((Measure.pi fun _ : Fin N => P).prod P) := by
  simpa only [Function.comp_def, sampleSnoc_apply] using
    ((sampleSnoc_preserving P N).integrable_comp_emb (sampleSnoc N).measurableEmbedding
      (g := F)).symm

theorem pi_snoc_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (F : (Fin (N + 1) → Ω) → ℝ) :
    (∫ ω, F ω ∂(Measure.pi fun _ : Fin (N + 1) => P)) =
      ∫ p : (Fin N → Ω) × Ω, F (Fin.snoc p.1 p.2)
        ∂((Measure.pi fun _ : Fin N => P).prod P) := by
  simpa only [sampleSnoc_apply] using
    ((sampleSnoc_preserving P N).integral_comp' F).symm


theorem pi_prefix_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (F : (Fin (N + 1) → Ω) → ℝ) (G : (Fin N → Ω) → ℝ)
    (hG : Integrable G (Measure.pi fun _ : Fin N => P))
    (heq : ∀ ω ξ, F (Fin.snoc ω ξ) = G ω) :
    Integrable F (Measure.pi fun _ : Fin (N + 1) => P) := by
  rw [pi_snoc_integrable_iff P N F]
  have hfun : (fun p : (Fin N → Ω) × Ω => F (Fin.snoc p.1 p.2)) =
      (fun p : (Fin N → Ω) × Ω => G p.1) := funext fun p => heq p.1 p.2
  rw [hfun]
  exact hG.comp_fst P

theorem pi_prefix_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (F : (Fin (N + 1) → Ω) → ℝ) (G : (Fin N → Ω) → ℝ)
    (heq : ∀ ω ξ, F (Fin.snoc ω ξ) = G ω) :
    (∫ ω, F ω ∂(Measure.pi fun _ : Fin (N + 1) => P)) =
      ∫ ω, G ω ∂(Measure.pi fun _ : Fin N => P) := by
  rw [pi_snoc_integral P N F]
  simp_rw [heq]
  rw [integral_fun_fst]
  simp

theorem measurable_run {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : ∀ t, Measurable (Function.uncurry (upd t)))
    (x0 : EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    Measurable (fun ω : Fin N → Ω => run upd x0 ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < N
    · simp only [run, dif_pos ht]
      exact (hupd t).comp (ih.prodMk (measurable_pi_apply ⟨t, ht⟩))
    · simpa only [run, dif_neg ht] using ih

theorem run_mem_U {d N : ℕ} {Ω : Type*}
    (U D : Set (EuclideanSpace ℝ (Fin d))) (hDU : D ⊆ U)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : ∀ t x ξ, upd t x ξ ∈ D)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U) (ω : Fin N → Ω) (t : ℕ) :
    run upd x0 ω t ∈ U := by
  induction t with
  | zero => exact hx0
  | succ t ih =>
    by_cases ht : t < N
    · simp only [run, dif_pos ht]
      exact hDU (hupd t _ _)
    · simpa only [run, dif_neg ht] using ih

theorem run_mem_D {d N : ℕ} {Ω : Type*}
    (D : Set (EuclideanSpace ℝ (Fin d)))
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : ∀ t x ξ, upd t x ξ ∈ D)
    (x0 : EuclideanSpace ℝ (Fin d)) (ω : Fin N → Ω) (t : ℕ)
    (ht0 : 0 < t) (htN : t ≤ N) : run upd x0 ω t ∈ D := by
  cases t with
  | zero => omega
  | succ t =>
    have ht : t < N := by omega
    simp only [run, dif_pos ht]
    exact hupd t _ _


/-- Transfer the exact one-step theorem to an independent, square-integrable random base. -/
theorem random_base_one_step {d : ℕ} {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (Q : Measure A) [IsProbabilityMeasure Q] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hr : IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : AssumptionB P U D f r model 0 (-μ) L Lfun)
    (β : ℕ → ℝ)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : IsAlg41Step P U D r model β upd)
    (t : ℕ) (hβ : 0 < β t) (X : A → EuclideanSpace ℝ (Fin d))
    (hXm : Measurable X) (hXU : ∀ a, X a ∈ U)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ D)
    (hstar : ∀ y ∈ D, f z + r z ≤ f y + r y)
    (hXsq : Integrable (fun a => ‖X a - z‖ ^ 2) Q) :
    Integrable (fun p : A × Ω => f (upd t (X p.1) p.2) + r (upd t (X p.1) p.2)) (Q.prod P) ∧
    Integrable (fun p : A × Ω => ‖upd t (X p.1) p.2 - z‖ ^ 2) (Q.prod P) ∧
    (∫ p : A × Ω, (f (upd t (X p.1) p.2) + r (upd t (X p.1) p.2) - (f z + r z)) +
      (β t + μ) / 2 * ‖upd t (X p.1) p.2 - z‖ ^ 2 ∂(Q.prod P)) ≤
      β t / 2 * (∫ a, ‖X a - z‖ ^ 2 ∂Q) + 2 * L ^ 2 / β t := by
  let V (p : A × Ω) := upd t (X p.1) p.2
  let gap (p : A × Ω) := f (V p) + r (V p) - (f z + r z)
  let sqdist (p : A × Ω) := ‖V p - z‖ ^ 2
  let F (p : A × Ω) := gap p + (β t + μ) / 2 * sqdist p
  let G (a : A) := β t / 2 * ‖X a - z‖ ^ 2 + 2 * L ^ 2 / β t
  have hVm : Measurable V :=
    (hupd.2.1 t).comp ((hXm.comp measurable_fst).prodMk measurable_snd)
  have hVD : ∀ p, V p ∈ D := fun p => hupd.1 t _ _
  have hrg : Measurable (fun p => r (V p)) :=
    Prove2MeS03.closed_epigraph_measurable_comp D r hr V hVm hVD
  have hgapm : Measurable gap := ((hf.continuous.measurable.comp hVm).add hrg).sub measurable_const
  have hsqm : Measurable sqdist := (hVm.sub measurable_const).norm.pow_const 2
  have hgap0 : ∀ p, 0 ≤ gap p := fun p => sub_nonneg.mpr (hstar _ (hVD p))
  have hsq0 : ∀ p, 0 ≤ sqdist p := fun p => sq_nonneg _
  have hc : 0 < (β t + μ) / 2 := by positivity
  have hFm : Measurable F := hgapm.add (hsqm.const_mul _)
  have hF0 : ∀ p, 0 ≤ F p := fun p => add_nonneg (hgap0 p) (mul_nonneg hc.le (hsq0 p))
  have hstep (a : A) := deterministic_one_step P U D f r model L Lfun μ hμ hr hf hB
    β upd hupd t hβ (X a) (hXU a) z hz hstar
  have hFi : ∀ a, Integrable (fun ξ => F (a, ξ)) P := by
    intro a
    exact ((hstep a).1.sub (integrable_const (f z + r z))).add
      ((hstep a).2.1.const_mul ((β t + μ) / 2))
  have hGi : Integrable G Q := (hXsq.const_mul (β t / 2)).add
    (integrable_const (2 * L ^ 2 / β t))
  have hbound : ∀ a, (∫ ξ, F (a, ξ) ∂P) ≤ G a := fun a => (hstep a).2.2
  obtain ⟨hFiProd, hE⟩ := Prove2MeS03.nonnegative_fiber_transfer Q P F hFm hF0 hFi G hGi hbound
  obtain ⟨hgapi, hsqi⟩ := integrable_nonneg_parts (Q.prod P) hFiProd
    hgapm.aestronglyMeasurable hsqm.aestronglyMeasurable hgap0 hsq0
    ((β t + μ) / 2) hc (Eventually.of_forall fun _ => le_rfl)
  refine ⟨?_, hsqi, ?_⟩
  · have hi : Integrable (fun p => gap p + (f z + r z)) (Q.prod P) :=
      hgapi.add (integrable_const (f z + r z))
    simpa only [gap, V, sub_add_cancel] using hi
  · have hGvalue : (∫ a, G a ∂Q) =
        β t / 2 * (∫ a, ‖X a - z‖ ^ 2 ∂Q) + 2 * L ^ 2 / β t := by
      dsimp only [G]
      rw [integral_add (hXsq.const_mul (β t / 2))
        (integrable_const (2 * L ^ 2 / β t)), integral_const_mul]
      simp
    rw [hGvalue] at hE
    exact hE


theorem run_prefix_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (N t : ℕ) (ht : t ≤ N)
    (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Integrable (fun ω : Fin N → Ω => F (run upd x0 ω t))
      (Measure.pi fun _ : Fin N => P)) :
    Integrable (fun ω : Fin (N + 1) → Ω => F (run upd x0 ω t))
      (Measure.pi fun _ : Fin (N + 1) => P) := by
  apply pi_prefix_integrable P N _ _ hF
  intro ω ξ
  rw [run_snoc_prefix upd x0 ω ξ t ht]

theorem run_prefix_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (N t : ℕ) (ht : t ≤ N)
    (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ ω : Fin (N + 1) → Ω, F (run upd x0 ω t) ∂(Measure.pi fun _ : Fin (N + 1) => P)) =
      ∫ ω : Fin N → Ω, F (run upd x0 ω t) ∂(Measure.pi fun _ : Fin N => P) := by
  apply pi_prefix_integral P N
  intro ω ξ
  rw [run_snoc_prefix upd x0 ω ξ t ht]

/-- All moments and one-step estimates on the same finite product sample space. -/
theorem finite_run_estimates {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hr : IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : AssumptionB P U D f r model 0 (-μ) L Lfun)
    (β : ℕ → ℝ) (hβ : ∀ t, 0 < β t)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : IsAlg41Step P U D r model β upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ D)
    (hstar : ∀ y ∈ D, f z + r z ≤ f y + r y) (N : ℕ) :
    (∀ t, t ≤ N → Integrable
      (fun ω : Fin N → Ω => f (run upd x0 ω t) + r (run upd x0 ω t))
      (Measure.pi fun _ : Fin N => P)) ∧
    (∀ t, t ≤ N → Integrable
      (fun ω : Fin N → Ω => ‖run upd x0 ω t - z‖ ^ 2)
      (Measure.pi fun _ : Fin N => P)) ∧
    (∀ t, t < N →
      (∫ ω : Fin N → Ω, (f (run upd x0 ω (t + 1)) + r (run upd x0 ω (t + 1)) - (f z + r z)) +
        (β t + μ) / 2 * ‖run upd x0 ω (t + 1) - z‖ ^ 2
          ∂(Measure.pi fun _ : Fin N => P)) ≤
        β t / 2 * (∫ ω : Fin N → Ω, ‖run upd x0 ω t - z‖ ^ 2
          ∂(Measure.pi fun _ : Fin N => P)) + 2 * L ^ 2 / β t) := by
  induction N with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      have ht0 : t = 0 := by omega
      subst t
      simpa only [run] using
        (integrable_const (μ := Measure.pi fun _ : Fin 0 => P) (f x0 + r x0))
    · intro t ht
      have ht0 : t = 0 := by omega
      subst t
      simpa only [run] using
        (integrable_const (μ := Measure.pi fun _ : Fin 0 => P) (‖x0 - z‖ ^ 2))
    · intro t ht
      omega
  | succ N ih =>
    rcases ih with ⟨hφ, hsq, hrec⟩
    have hrandom := random_base_one_step (Measure.pi fun _ : Fin N => P) P
      U D f r model L Lfun μ hμ hr hf hB β upd hupd N (hβ N)
      (fun ω : Fin N → Ω => run upd x0 ω N)
      (measurable_run upd hupd.2.1 x0 N)
      (fun ω => run_mem_U U D hB.2.2.1 upd hupd.1 x0 hx0 ω N)
      z hz hstar (hsq N le_rfl)
    have hφlast : Integrable
        (fun ω : Fin (N + 1) → Ω => f (run upd x0 ω (N + 1)) + r (run upd x0 ω (N + 1)))
        (Measure.pi fun _ : Fin (N + 1) => P) := by
      apply (pi_snoc_integrable_iff P N _).mpr
      simpa only [run_snoc_last] using hrandom.1
    have hsqlast : Integrable
        (fun ω : Fin (N + 1) → Ω => ‖run upd x0 ω (N + 1) - z‖ ^ 2)
        (Measure.pi fun _ : Fin (N + 1) => P) := by
      apply (pi_snoc_integrable_iff P N _).mpr
      simpa only [run_snoc_last] using hrandom.2.1
    have hreclast :
        (∫ ω : Fin (N + 1) → Ω,
          (f (run upd x0 ω (N + 1)) + r (run upd x0 ω (N + 1)) - (f z + r z)) +
            (β N + μ) / 2 * ‖run upd x0 ω (N + 1) - z‖ ^ 2
              ∂(Measure.pi fun _ : Fin (N + 1) => P)) ≤
          β N / 2 * (∫ ω : Fin (N + 1) → Ω, ‖run upd x0 ω N - z‖ ^ 2
            ∂(Measure.pi fun _ : Fin (N + 1) => P)) + 2 * L ^ 2 / β N := by
      rw [pi_snoc_integral P N (fun ω =>
        (f (run upd x0 ω (N + 1)) + r (run upd x0 ω (N + 1)) - (f z + r z)) +
          (β N + μ) / 2 * ‖run upd x0 ω (N + 1) - z‖ ^ 2)]
      simp_rw [run_snoc_last]
      rw [run_prefix_integral P upd x0 N N le_rfl (fun y => ‖y - z‖ ^ 2)]
      exact hrandom.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      by_cases htN : t ≤ N
      · exact run_prefix_integrable P upd x0 N t htN (fun y => f y + r y) (hφ t htN)
      · have hteq : t = N + 1 := by omega
        subst t
        exact hφlast
    · intro t ht
      by_cases htN : t ≤ N
      · exact run_prefix_integrable P upd x0 N t htN (fun y => ‖y - z‖ ^ 2) (hsq t htN)
      · have hteq : t = N + 1 := by omega
        subst t
        exact hsqlast
    · intro t ht
      by_cases htN : t < N
      · rw [run_prefix_integral P upd x0 N (t + 1) (by omega)
          (fun y => (f y + r y - (f z + r z)) + (β t + μ) / 2 * ‖y - z‖ ^ 2),
          run_prefix_integral P upd x0 N t (by omega) (fun y => ‖y - z‖ ^ 2)]
        exact hrec t htN
      · have hteq : t = N := by omega
        subst t
        exact hreclast


end Prove2MeS03.P094

-- Source component: P094_objective_convexity

open MeasureTheory

namespace Prove2MeS03

theorem convex_of_negative_weak_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : Set E} {g : E → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ConvexOn ℝ D (fun y => g y + (-μ) / 2 * ‖y‖ ^ 2)) :
    ConvexOn ℝ D g := by
  have hs : StrongConvexOn D μ g := by
    apply strongConvexOn_iff_convex.mpr
    simpa only [neg_div, neg_mul, sub_eq_add_neg] using h
  exact strongConvexOn_zero.mp (StrongConvexOn.mono hμ hs)

/-- At the convex combination, use the model based at that very point.
Expected touching identifies its value, and one-sided accuracy bounds the
two endpoint values. -/
theorem objective_convex_from_models
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set E) (hD : D.Nonempty) (hDU : D ⊆ U)
    (f r : E → ℝ) (model : E → E → Ω → ℝ)
    (hint : ∀ x ∈ U, ∀ y ∈ U, Integrable (fun ξ => model x y ξ) P)
    (htouch : ∀ x ∈ U, (∫ ξ, model x x ξ ∂P) = f x)
    (haccuracy : ∀ x ∈ U, ∀ y ∈ U, (∫ ξ, model x y ξ - f y ∂P) ≤ 0)
    (hconv : ∀ x ∈ U, ∀ᵐ ξ ∂P, ConvexOn ℝ D (fun y => model x y ξ + r y)) :
    ConvexOn ℝ D (fun y => f y + r y) := by
  have hDconv : Convex ℝ D := by
    obtain ⟨x, hx⟩ := hD
    obtain ⟨ξ, hξ⟩ := (hconv x (hDU hx)).exists
    exact hξ.1
  refine ⟨hDconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hzD : z ∈ D := hDconv hx hy ha hb hab
  have hzU : z ∈ U := hDU hzD
  have hxi := hint z hzU x (hDU hx)
  have hyi := hint z hzU y (hDU hy)
  have hzi := hint z hzU z hzU
  have hp : ∀ᵐ ξ ∂P, model z z ξ + r z ≤
      a * (model z x ξ + r x) + b * (model z y ξ + r y) :=
    (hconv z hzU).mono (fun ξ hξ => by
      simpa only [z, smul_eq_mul] using hξ.2 hx hy ha hb hab)
  have hxa : Integrable (fun ξ => a * (model z x ξ + r x)) P :=
    (hxi.add (integrable_const (r x))).const_mul a
  have hyb : Integrable (fun ξ => b * (model z y ξ + r y)) P :=
    (hyi.add (integrable_const (r y))).const_mul b
  have hm := integral_mono_ae (hzi.add (integrable_const (r z)))
    (hxa.add hyb) hp
  change (∫ ξ, model z z ξ + r z ∂P) ≤
    ∫ ξ, a * (model z x ξ + r x) + b * (model z y ξ + r y) ∂P at hm
  rw [integral_add hzi (integrable_const (r z)),
    integral_add hxa hyb,
    integral_const_mul, integral_const_mul,
    integral_add hxi (integrable_const (r x)), integral_add hyi (integrable_const (r y)),
    htouch z hzU] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  have hax := haccuracy z hzU x (hDU hx)
  have hay := haccuracy z hzU y (hDU hy)
  rw [integral_sub hxi (integrable_const (f x))] at hax
  rw [integral_sub hyi (integrable_const (f y))] at hay
  simp only [integral_const, probReal_univ, one_smul] at hax hay
  have hax' := mul_le_mul_of_nonneg_left (show (∫ ξ, model z x ξ ∂P) ≤ f x by linarith) ha
  have hay' := mul_le_mul_of_nonneg_left (show (∫ ξ, model z y ξ ∂P) ≤ f y by linarith) hb
  change f z + r z ≤ a * (f x + r x) + b * (f y + r y)
  linarith

end Prove2MeS03

-- Source component: P094_average_jensen

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace P094Average

theorem finite_average_integrable_gap
    {ι Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [Module ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] (D : Set E) (φ : E → ℝ) (lower : ℝ)
    (s : Finset ι) (w : ι → ℝ) (X : ι → Ω → E)
    (hφ : ConvexOn ℝ D φ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : ∑ i ∈ s, w i = 1)
    (hX : ∀ i ∈ s, ∀ ω, X i ω ∈ D)
    (hlower : ∀ x ∈ D, lower ≤ φ x)
    (hmeas : AEStronglyMeasurable (fun ω => φ (∑ i ∈ s, w i • X i ω)) P)
    (hI : ∀ i ∈ s, Integrable (fun ω => φ (X i ω)) P) :
    (∀ ω, (∑ i ∈ s, w i • X i ω) ∈ D) ∧
    Integrable (fun ω => φ (∑ i ∈ s, w i • X i ω)) P ∧
    (∫ ω, (φ (∑ i ∈ s, w i • X i ω) - lower) ∂P) ≤
      ∑ i ∈ s, w i * (∫ ω, (φ (X i ω) - lower) ∂P) := by
  have hmem : ∀ ω, (∑ i ∈ s, w i • X i ω) ∈ D :=
    fun ω => hφ.1.sum_mem hw hwsum (fun i hi => hX i hi ω)
  have hpoint : ∀ ω,
      φ (∑ i ∈ s, w i • X i ω) - lower ≤
        ∑ i ∈ s, w i * (φ (X i ω) - lower) := by
    intro ω
    have h := hφ.map_sum_le hw hwsum (fun i hi => hX i hi ω)
    simp only [smul_eq_mul] at h
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum, one_mul]
    exact sub_le_sub_right h lower
  have hterm : ∀ i ∈ s,
      Integrable (fun ω => w i * (φ (X i ω) - lower)) P :=
    fun i hi => ((hI i hi).sub (integrable_const lower)).const_mul (w i)
  have hsum : Integrable (fun ω => ∑ i ∈ s, w i * (φ (X i ω) - lower)) P :=
    integrable_finsetSum s hterm
  have hgap : Integrable (fun ω => φ (∑ i ∈ s, w i • X i ω) - lower) P :=
    hsum.mono_nonneg (hmeas.sub aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun ω => sub_nonneg.mpr (hlower _ (hmem ω)))
      (Filter.Eventually.of_forall hpoint)
  refine ⟨hmem, ?_, ?_⟩
  · exact (hgap.add (integrable_const lower)).congr
      (Filter.Eventually.of_forall fun ω => sub_add_cancel _ _)
  · calc
      (∫ ω, (φ (∑ i ∈ s, w i • X i ω) - lower) ∂P) ≤
          ∫ ω, ∑ i ∈ s, w i * (φ (X i ω) - lower) ∂P :=
        integral_mono_ae hgap hsum (Filter.Eventually.of_forall hpoint)
      _ = ∑ i ∈ s, w i * (∫ ω, (φ (X i ω) - lower) ∂P) := by
        rw [integral_finsetSum s hterm]
        simp only [integral_const_mul]

theorem sum_shifted_weights (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1)) =
      (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2) / 2 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (T + 1) + 1), ih]
      push_cast
      ring

theorem average_denominator_pos (T : ℕ) :
    0 < ((T : ℝ) + 2) * ((T : ℝ) + 3) - 2 := by
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith

theorem normalized_weights_sum (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 (T + 1),
      (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) * ((t : ℝ) + 1)) = 1 := by
  rw [← Finset.mul_sum, sum_shifted_weights]
  field_simp [ne_of_gt (average_denominator_pos T)]

theorem normalized_weights_nonneg (T t : ℕ) :
    0 ≤ (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) * ((t : ℝ) + 1) :=
  mul_nonneg (div_nonneg (by norm_num) (le_of_lt (average_denominator_pos T)))
    (by positivity)

theorem normalized_average_integrable_gap
    {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [Module ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] (D : Set E) (φ : E → ℝ) (lower : ℝ)
    (X : ℕ → Ω → E) (T : ℕ) (hφ : ConvexOn ℝ D φ)
    (hX : ∀ t ∈ Finset.Icc 1 (T + 1), ∀ ω, X t ω ∈ D)
    (hlower : ∀ x ∈ D, lower ≤ φ x)
    (hmeas : AEStronglyMeasurable (fun ω => φ
      ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
        ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω)) P)
    (hI : ∀ t ∈ Finset.Icc 1 (T + 1), Integrable (fun ω => φ (X t ω)) P) :
    (∀ ω, ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
      ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω) ∈ D) ∧
    Integrable (fun ω => φ
      ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
        ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω)) P ∧
    (∫ ω, (φ ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
        ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω) - lower) ∂P) ≤
      (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) *
        ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) *
          (∫ ω, (φ (X t ω) - lower) ∂P) := by
  simpa only [mul_smul, ← Finset.smul_sum, ← Finset.mul_sum, mul_assoc] using
    finite_average_integrable_gap P D φ lower (Finset.Icc 1 (T + 1))
      (fun t => (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) * ((t : ℝ) + 1))
      X hφ (fun t _ => normalized_weights_nonneg T t) (normalized_weights_sum T)
      hX hlower (by simpa only [mul_smul, ← Finset.smul_sum] using hmeas) hI

theorem measurable_normalized_average
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E] [MeasurableAdd₂ E] [MeasurableConstSMul ℝ E]
    (X : ℕ → Ω → E) (T : ℕ)
    (hX : ∀ t ∈ Finset.Icc 1 (T + 1), Measurable (X t)) :
    Measurable (fun ω =>
      (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
        ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω) := by
  exact (Finset.measurable_sum _ fun t ht => (hX t ht).const_smul ((t : ℝ) + 1)).const_smul _

end P094Average


-- Source component: P094_telescope

open scoped BigOperators
namespace Prove2MeS03

/-- Multiply the corrected one-step estimate by its cancellation weight. -/
theorem weighted_one_step (t : ℕ) (μ L d₀ d₁ g : ℝ) (hμ : 0 < μ)
    (hstep : g + (μ * ((t : ℝ) + 1) / 2 + μ) / 2 * d₁ ≤
      (μ * ((t : ℝ) + 1) / 2) / 2 * d₀ + 2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2)) :
    ((t : ℝ) + 2) * g + μ / 4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) * d₁ ≤
      μ / 4 * ((t : ℝ) + 1) * ((t : ℝ) + 2) * d₀ + 8 * L ^ 2 / μ := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hβ : 0 < μ * ((t : ℝ) + 1) / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (t : ℝ) + 2 by positivity)
  have herr : ((t : ℝ) + 2) * (2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2)) ≤
      8 * L ^ 2 / μ := by
    have heq : ((t : ℝ) + 2) * (2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2)) =
        (4 * ((t : ℝ) + 2) * L ^ 2) / (μ * ((t : ℝ) + 1)) := by
      field_simp
      <;> ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos hμ ht1)).mpr
    have heq' : 8 * L ^ 2 / μ * (μ * ((t : ℝ) + 1)) =
        8 * L ^ 2 * ((t : ℝ) + 1) := by
      field_simp
    rw [heq']
    have hsq : 0 ≤ L ^ 2 := sq_nonneg L
    have hprod : 0 ≤ (t : ℝ) * L ^ 2 := mul_nonneg ht hsq
    nlinarith
  nlinarith

/-- The weighted distance terms cancel exactly over the finite run. -/
theorem weighted_potential_telescope
    (μ L : ℝ) (hμ : 0 < μ) (D G : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ t < N,
      ((t : ℝ) + 2) * G (t + 1) + μ / 4 * ((t : ℝ) + 2) * ((t : ℝ) + 3) * D (t + 1) ≤
        μ / 4 * ((t : ℝ) + 1) * ((t : ℝ) + 2) * D t + 8 * L ^ 2 / μ) :
    (∑ t ∈ Finset.range N, ((t : ℝ) + 2) * G (t + 1)) +
      μ / 4 * ((N : ℝ) + 1) * ((N : ℝ) + 2) * D N ≤
        μ / 2 * D 0 + (N : ℝ) * (8 * L ^ 2 / μ) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]; ring_nf; rfl
  | succ N ih =>
    have hprev := ih (fun t ht => hstep t (Nat.lt.step ht))
    have hlast := hstep N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith


/-- Shift the finite-run indexing to the published interval of iterates. -/
theorem sum_Icc_one_eq_range {A : Type*} [AddCommMonoid A] (f : ℕ → A) (N : ℕ) :
    (∑ t ∈ Finset.Icc 1 N, f t) = ∑ t ∈ Finset.range N, f (t + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

/-- The scalar cancellation gives the exact constants and normalization of Theorem 4.2. -/
theorem averaged_telescope_bound (μ L : ℝ) (hμ : 0 < μ) (D G : ℕ → ℝ) (T : ℕ)
    (hD0 : 0 ≤ D 0) (hDN : 0 ≤ D (T + 1))
    (hstep : ∀ t < T + 1,
      G (t + 1) + (μ * ((t : ℝ) + 1) / 2 + μ) / 2 * D (t + 1) ≤
        (μ * ((t : ℝ) + 1) / 2) / 2 * D t + 2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2)) :
    (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) *
        (∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) * G t) ≤
      μ * D 0 / ((T : ℝ) + 2) ^ 2 + 16 * L ^ 2 / (μ * ((T : ℝ) + 2)) := by
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hT1 : 0 < (T : ℝ) + 1 := by positivity
  have hT2 : 0 < (T : ℝ) + 2 := by positivity
  have hT4 : 0 < (T : ℝ) + 4 := by positivity
  have hden : ((T : ℝ) + 2) * ((T : ℝ) + 3) - 2 =
      ((T : ℝ) + 1) * ((T : ℝ) + 4) := by ring
  have htel := weighted_potential_telescope μ L hμ D G (T + 1)
    (fun t ht => weighted_one_step t μ L (D t) (D (t + 1)) (G (t + 1)) hμ (hstep t ht))
  have hpot : 0 ≤ μ / 4 * (((T + 1 : ℕ) : ℝ) + 1) *
      (((T + 1 : ℕ) : ℝ) + 2) * D (T + 1) := by positivity
  have hsum : (∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) * G t) ≤
      μ / 2 * D 0 + ((T : ℝ) + 1) * (8 * L ^ 2 / μ) := by
    rw [sum_Icc_one_eq_range]
    simp only [Nat.cast_add, Nat.cast_one] at htel hpot ⊢
    have heq : (∑ t ∈ Finset.range (T + 1), ((t : ℝ) + 1 + 1) * G (t + 1)) =
        ∑ t ∈ Finset.range (T + 1), ((t : ℝ) + 2) * G (t + 1) := by
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      ring
    rw [heq]
    linarith
  rw [hden]
  have hc : 0 ≤ 2 / (((T : ℝ) + 1) * ((T : ℝ) + 4)) := by positivity
  calc
    _ ≤ (2 / (((T : ℝ) + 1) * ((T : ℝ) + 4))) *
        (μ / 2 * D 0 + ((T : ℝ) + 1) * (8 * L ^ 2 / μ)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = μ * D 0 / (((T : ℝ) + 1) * ((T : ℝ) + 4)) +
        16 * L ^ 2 / (μ * ((T : ℝ) + 4)) := by
      field_simp
      <;> ring
    _ ≤ μ * D 0 / ((T : ℝ) + 2) ^ 2 + 16 * L ^ 2 / (μ * ((T : ℝ) + 2)) := by
      apply add_le_add
      · apply div_le_div_of_nonneg_left (mul_nonneg hμ.le hD0) (sq_pos_of_pos hT2)
        nlinarith
      · apply div_le_div_of_nonneg_left (by positivity) (mul_pos hμ hT2)
        nlinarith

end Prove2MeS03

theorem solution {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hD : D.Nonempty) (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model 0 (-μ) L Lfun)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : StochModelWC.ModelBased.IsAlg41Step P U D r model (fun t => μ * ((t : ℝ) + 1) / 2) upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ D)
    (hmin : ∀ y ∈ D, f xstar + r xstar ≤ f y + r y)
    (T : ℕ) (hT : 0 < T) :
    Integrable (fun ω : Fin (T + 1) → Ω =>
        f ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
            ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
          + r ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
            ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t))
      (Measure.pi fun _ : Fin (T + 1) => P) ∧
    ∫ ω, (f ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
              ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
            + r ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
              ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
            - (f xstar + r xstar)) ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
      μ * ‖x0 - xstar‖ ^ 2 / ((T : ℝ) + 2) ^ 2 + 16 * L ^ 2 / (μ * ((T : ℝ) + 2))  := by
  classical
  let Q : Measure (Fin (T + 1) → Ω) := Measure.pi fun _ : Fin (T + 1) => P
  let X (t : ℕ) (ω : Fin (T + 1) → Ω) := StochModelWC.ModelBased.run upd x0 ω t
  let φ (x : EuclideanSpace ℝ (Fin d)) := f x + r x
  let β (t : ℕ) := μ * ((t : ℝ) + 1) / 2
  have hβ : ∀ t, 0 < β t := by
    intro t
    dsimp [β]
    positivity
  obtain ⟨hφi, hdi, hrec⟩ := Prove2MeS03.P094.finite_run_estimates
    P U D f r model L Lfun μ hμ hr hf hB β hβ upd hupd x0 hx0 xstar hxstar hmin (T + 1)
  have hconv : ConvexOn ℝ D φ := by
    rcases hB with ⟨hUo, hUc, hDU, hMj, hMint, htouch, hacc, hweak, hLm, hL0, hLsq, hLb, hB4⟩
    refine Prove2MeS03.objective_convex_from_models P U D hD hDU f r model hMint htouch ?_ ?_
    · intro x hx y hy
      simpa only [zero_div, zero_mul] using hacc x hx y hy
    · intro x hx
      exact (hweak x hx).mono (fun ξ hξ =>
        Prove2MeS03.convex_of_negative_weak_parameter hμ.le hξ)
  have hXD : ∀ t ∈ Finset.Icc 1 (T + 1), ∀ ω, X t ω ∈ D := by
    intro t ht ω
    exact Prove2MeS03.P094.run_mem_D D upd hupd.1 x0 ω t
      (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  have hXm : ∀ t ∈ Finset.Icc 1 (T + 1), Measurable (X t) :=
    fun t _ => Prove2MeS03.P094.measurable_run upd hupd.2.1 x0 t
  let avg (ω : Fin (T + 1) → Ω) :=
    (2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
      ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • X t ω
  have hAvgD : ∀ ω, avg ω ∈ D := by
    intro ω
    have hm := hconv.1.sum_mem
      (fun t (_ : t ∈ Finset.Icc 1 (T + 1)) => P094Average.normalized_weights_nonneg T t)
      (P094Average.normalized_weights_sum T) (fun t ht => hXD t ht ω)
    simpa only [avg, mul_smul, ← Finset.smul_sum] using hm
  have hAvgm : Measurable avg := P094Average.measurable_normalized_average X T hXm
  have hφAvgm : Measurable (fun ω => φ (avg ω)) :=
    (hf.continuous.measurable.comp hAvgm).add
      (Prove2MeS03.closed_epigraph_measurable_comp D r hr avg hAvgm hAvgD)
  have hφXi : ∀ t ∈ Finset.Icc 1 (T + 1), Integrable (fun ω => φ (X t ω)) Q :=
    fun t ht => hφi t (Finset.mem_Icc.mp ht).2
  obtain ⟨hAvgD', hAvgi, hJ⟩ := P094Average.normalized_average_integrable_gap
    Q D φ (φ xstar) X T hconv hXD hmin hφAvgm.aestronglyMeasurable hφXi
  let dist (t : ℕ) := ∫ ω, ‖X t ω - xstar‖ ^ 2 ∂Q
  let gap (t : ℕ) := ∫ ω, (φ (X t ω) - φ xstar) ∂Q
  have hscalar : ∀ t < T + 1,
      gap (t + 1) + (μ * ((t : ℝ) + 1) / 2 + μ) / 2 * dist (t + 1) ≤
        (μ * ((t : ℝ) + 1) / 2) / 2 * dist t + 2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2) := by
    intro t ht
    have hp := hrec t ht
    have hti : t + 1 ≤ T + 1 := Nat.succ_le_of_lt ht
    have hgi : Integrable (fun ω : Fin (T + 1) → Ω =>
        f (StochModelWC.ModelBased.run upd x0 ω (t + 1)) +
        r (StochModelWC.ModelBased.run upd x0 ω (t + 1)) - (f xstar + r xstar)) Q :=
      (hφi (t + 1) hti).sub (integrable_const (f xstar + r xstar))
    have hsi : Integrable (fun ω : Fin (T + 1) → Ω =>
        (β t + μ) / 2 * ‖StochModelWC.ModelBased.run upd x0 ω (t + 1) - xstar‖ ^ 2) Q :=
      (hdi (t + 1) hti).const_mul ((β t + μ) / 2)
    rw [integral_add hgi hsi, integral_const_mul] at hp
    exact hp
  have hdist0 : dist 0 = ‖x0 - xstar‖ ^ 2 := by
    simp [dist, X, Q, StochModelWC.ModelBased.run]
  have hnonneg (t : ℕ) : 0 ≤ dist t := integral_nonneg (fun _ => sq_nonneg _)
  have htel := Prove2MeS03.averaged_telescope_bound μ L hμ dist gap T
    (hnonneg 0) (hnonneg (T + 1)) hscalar
  rw [hdist0] at htel
  exact ⟨hAvgi, hJ.trans htel⟩

#print axioms solution
