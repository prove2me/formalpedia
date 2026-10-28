-- Prove2me | solution 1 for OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:59:37.338428+00:00
-- url     : https://prove2.me/submissions/07d7b022-bd1d-4740-8ab5-940149c2a7ef

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_bounded_entropy_subdifferential

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_NonnegativeParallelogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable {q : V → ℝ} (hq : NonnegativeParallelogram q)
include hq

lemma NonnegativeParallelogram.polar_cauchySchwarz (f g : V) :
    (energyPolar q f g)^2 ≤ q f * q g := by
  have H : ∀ t : ℝ, 0 ≤ q f + 2*t*energyPolar q f g + t^2*q g := by
    intro t
    have h := hq.nonneg (f + t • g)
    rw [hq.polar_add, hq.polar_comm f, hq.polar_smul_left, hq.polar_comm g, hq.smul] at h
    nlinarith
  by_cases hg : q g = 0
  · have h1 := H (-(q f+1)/(2*energyPolar q f g))
    by_cases hp : energyPolar q f g = 0
    · simp [hp, hg]
    · have heq : q f + 2 * (-(q f+1)/(2*energyPolar q f g)) * energyPolar q f g +
          (-(q f+1)/(2*energyPolar q f g))^2 * q g = -1 := by
        rw [hg]
        field_simp [hp]
        ring
      rw [heq] at h1
      linarith
  · have h1 := H (-energyPolar q f g/q g)
    have hgpos : 0 < q g := lt_of_le_of_ne (hq.nonneg g) (Ne.symm hg)
    field_simp at h1
    nlinarith [sq_nonneg (energyPolar q f g)]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientTendstoNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

section NormConvergence
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_tendsto_of_norm_tendsto {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) := by
  let fm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • fn n + (1/2 : ℝ) • f
  let Dm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • Dn n + (1/2 : ℝ) • D
  have hmid (n : ℕ) : IsLocalWeakUpperGradient m (fm n) (Dm n) := by
    exact convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (fn n, Dn n)) (y := WithLp.toLp 2 (f,D))
      (hn n) hD (by norm_num) (by norm_num) (by norm_num)
  have hfm : Tendsto fm atTop (𝓝 f) := by
    have H := (hf.const_smul (1/2 : ℝ)).add
      (tendsto_const_nhds (x := (1/2 : ℝ) • f))
    simpa only [← add_smul, show (1/2:ℝ)+(1/2)=1 by norm_num, one_smul] using H
  have hlow (a : ℝ) (ha : a < ‖D‖) : ∀ᶠ n in atTop, a < ‖Dm n‖ := by
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    have H := hfm.eventually ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)
    filter_upwards [H] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dm n,hmid n,hle⟩)
  have hupper (n : ℕ) : ‖Dm n‖ ≤ (‖Dn n‖+‖D‖)/2 := by
    calc
      ‖Dm n‖ ≤ ‖(1/2 : ℝ) • Dn n‖ + ‖(1/2 : ℝ) • D‖ := norm_add_le _ _
      _ = (‖Dn n‖+‖D‖)/2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        ring
  have hmajor : Tendsto (fun n => (‖Dn n‖+‖D‖)/2) atTop (𝓝 ‖D‖) := by
    convert (hNorm.add_const ‖D‖).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hmidNorm : Tendsto (fun n => ‖Dm n‖) atTop (𝓝 ‖D‖) := by
    apply tendsto_order.mpr
    refine ⟨hlow, fun b hb => ?_⟩
    filter_upwards [hmajor.eventually (gt_mem_nhds hb)] with n hn'
    exact (hupper n).trans_lt hn'
  have hsq (n : ℕ) : ‖Dn n - D‖^2 = 2*‖Dn n‖^2+2*‖D‖^2-4*‖Dm n‖^2 := by
    have hm : ‖Dm n‖ = ‖Dn n+D‖/2 := by
      simp only [Dm, ← smul_add, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      ring
    rw [hm]
    nlinarith [parallelogram_law_with_norm ℝ (Dn n) D]
  have hs : Tendsto (fun n => ‖Dn n-D‖^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    convert ((hNorm.pow 2).const_mul 2 |>.add_const (2*‖D‖^2)).sub
      ((hmidNorm.pow 2).const_mul 4) using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using H

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.norm_le {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    {E : Lp ℝ 2 m} (hE : IsLocalWeakUpperGradient m f E) : ‖D‖ ≤ ‖E‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hD.2 E hE, hD.1.2.1, hE.2.1] with x hx hd he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg he] using hx

lemma IsMinimalLocalWeakUpperGradient.tendsto_of_norm_tendsto
    {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) :=
  upperGradient_tendsto_of_norm_tendsto hn hf hD.1 (fun _ hE => hD.norm_le hE) hNorm
end NormConvergence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CcConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]

lemma exists_marginal_majorant (h : C_c(X×Y,ℝ)) :
    ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ), h ≤ marginalSum fg := by
  refine ⟨(ccConst X ‖h.toContinuousMap‖,0), ?_⟩
  intro p
  change h.toContinuousMap p ≤ ‖h.toContinuousMap‖ + 0
  simpa only [add_zero] using h.toContinuousMap.apply_le_norm p

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

lemma integral_marginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    ∫ p, marginalSum fg p ∂μ.prod ν = marginalIntegral μ ν fg := by
  rw [integral_prod _ (marginalSum fg).integrable]
  simp only [marginalSum_apply, marginalIntegral_apply]
  have H (x : X) : (∫ y, (fg.1 x + fg.2 y) ∂ν) = fg.1 x + ∫ y, fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) fg.2.integrable]
    simp
  simp_rw [H]
  rw [integral_add fg.1.integrable (integrable_const _)]
  simp

lemma exists_measure_of_positive_functional
    (g : C_c(X,ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure X, IsFiniteMeasure q ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂q) = g f := by
  let Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ := { g with monotone' := hg }
  exact ⟨RealRMK.rieszMeasure Λ, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), RealRMK.integral_rieszMeasure Λ⟩

omit [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y] [BorelSpace X] [BorelSpace Y] in
lemma probability_of_first_marginal {μ : Measure X} [IsProbabilityMeasure μ]
    {q : Measure (X×Y)} (hfst : q.map Prod.fst = μ) : IsProbabilityMeasure q := by
  constructor
  have H := congrArg (fun η : Measure X => η univ) hfst
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    measure_univ] using H

lemma integral_marginalSum_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    (hfst : q.map Prod.fst = μ) (hsnd : q.map Prod.snd = ν)
    (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg := by
  let _ := probability_of_first_marginal hfst
  have h0 : Integrable (fun p : X×Y => fg.1 p.1) q :=
    (fg.1.continuous.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun p : X×Y => fg.2 p.2) q :=
    (fg.2.continuous.comp continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ p, fg.1 p.1+fg.2 p.2 ∂q) = _
  rw [integral_add h0 h1]
  rw [← integral_map (μ := q) (f := fg.1) measurable_fst.aemeasurable (map_continuous fg.1).aestronglyMeasurable,
    ← integral_map (μ := q) (f := fg.2) measurable_snd.aemeasurable (map_continuous fg.2).aestronglyMeasurable,
    hfst, hsnd]
  rfl

lemma marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    [IsFiniteMeasure q]
    (hq : ∀ fg : C_c(X,ℝ) × C_c(Y,ℝ),
      (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, add_zero, integral_zero] using hq (f,0)
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, zero_add, integral_zero] using hq (0,f)

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_QuadraticCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance ccPosSMulMono : PosSMulMono ℝ C_c(X×Y,ℝ) where
  smul_le_smul_of_nonneg_left r hr f g hfg := by
    intro p
    exact mul_le_mul_of_nonneg_left (hfg p) hr

lemma compact_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : C_c(X×Y,ℝ)) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×Y), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, cost p ∂q) ≤ ∫ p, cost p ∂q') ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ),
        marginalSum fg ≤ cost ∧
        (∫ p, cost p ∂q) < marginalIntegral μ ν fg + ε := by
  let T : (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] C_c(X×Y,ℝ) := marginalSum
  let c := marginalIntegral μ ν
  let l := (integralPositiveLinearMap (μ.prod ν)).toLinearMap
  have hl : Monotone l := (integralPositiveLinearMap (μ.prod ν)).monotone
  have hcomp : ∀ fg, l (T fg) = c fg := integral_marginalSum μ ν
  have hmajor : ∀ h, ∃ fg, h ≤ T fg := exists_marginal_majorant
  obtain ⟨g,hgpos,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hqfinite,hq⟩ := exists_measure_of_positive_functional g hgpos
  let _ := hqfinite
  have hqsum (fg) : (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg :=
    (hq (T fg)).trans (hgmarg fg)
  obtain ⟨hq0,hq1⟩ := marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p, cost p ∂q) = - upperEnvelope T c (-cost) := by
    have H := (hq (-cost)).trans hgcost
    change (∫ p, -cost p ∂q) = upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    linarith
  refine ⟨q, probability_of_first_marginal hq0, hq0, hq1, ?_, ?_⟩
  · intro q' hq'0 hq'1
    let _ := probability_of_first_marginal hq'0
    let l' := (integralPositiveLinearMap q').toLinearMap
    have hl' : Monotone l' := (integralPositiveLinearMap q').monotone
    have hcomp' : ∀ fg, l' (T fg) = c fg := integral_marginalSum_of_marginals μ ν hq'0 hq'1
    have H := lower_le_envelope T c l' hl' hcomp' hmajor (-cost)
    change (∫ p, -cost p ∂q') ≤ upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    rw [hcq]
    linarith
  · intro ε hε
    obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
      (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
    refine ⟨-fg, ?_, ?_⟩
    · change T (-fg) ≤ cost
      rw [map_neg]
      simpa only [neg_neg] using neg_le_neg hfg
    · change (∫ p, cost p ∂q) < c (-fg)+ε
      rw [hcq, map_neg]
      linarith

end WeakHessianTransport

open Set Filter
open scoped Topology ENNReal NNReal


open Set

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_QuadraticCostIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open Set Filter MeasureTheory CompactlySupported
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma quadratic_cost_increment {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (x z y : X) :
    dist z y^2/2-dist x y^2/2 ≤ (R:ℝ)*dist z x := by
  have h1 := dist_triangle z x y
  have h2 := hR z y
  have h3 := hR x y
  have h4 := dist_nonneg (x := z) (y := y)
  have h5 := dist_nonneg (x := x) (y := y)
  have h6 := dist_nonneg (x := z) (y := x)
  have H : (dist z y-dist x y)*(dist z y+dist x y) ≤ dist z x*(2*(R:ℝ)) := by
    calc
      _ ≤ dist z x*(dist z y+dist x y) := by gcongr; linarith
      _ ≤ dist z x*(2*(R:ℝ)) := by gcongr; linarith
  nlinarith

lemma hopfLax_lipschitz_diameter {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    {f : X → ℝ} {B : ℝ} (hf : Continuous f) (hB : ∀ x, B ≤ f x) :
    LipschitzWith R (hopfLax f 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  have H (z x : X) : hopfLax f 1 z-hopfLax f 1 x ≤ (R:ℝ)*dist z x := by
    obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hB (by norm_num : (0:ℝ)<1) x
    have hz := hopfLax_le_objective hB (by norm_num : (0:ℝ)<1) z y
    have hi := quadratic_cost_increment hR x z y
    rw [← hy]
    dsimp [hopfObjective] at *
    linarith
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by have HH := H x z; rw [dist_comm x z] at HH; linarith, H z x⟩

lemma isCompact_lipschitz_norm_ball (R : ℝ≥0) {M : ℝ} (_hM : 0 ≤ M) :
    IsCompact {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M} := by
  let S := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M}
  have hS : IsClosed S :=
    ((isClosed_setOfPred_lipschitzWith R).preimage (continuous_pi fun x : X => continuous_eval_const x)).inter
      (isClosed_le continuous_norm continuous_const)
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  have hb : IsClosed (e '' S) := e.toHomeomorph.isClosedMap S hS
  have hc : IsCompact (e '' S) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Icc (-M) M) isCompact_Icc (e '' S) hb
    · rintro f x ⟨φ,hφ,rfl⟩
      exact abs_le.mp ((φ.norm_coe_le_norm x).trans hφ.2)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (R:ℝ)*r)
        (by simpa only [mul_zero, id_eq] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (R:ℝ))
      intro x y f
      obtain ⟨φ,hφ,he⟩ := f.property
      have hed : (f.val : X → ℝ) = φ := by rw [← he]; rfl
      change dist (f.val x) (f.val y) ≤ (R:ℝ)*dist x y
      rw [congrFun hed x,congrFun hed y]
      exact hφ.1.dist_le_mul x y
  exact e.toHomeomorph.isCompact_image.mp hc

variable [MeasurableSpace X] [BorelSpace X]
lemma potential_integral_lipschitz (μ : Measure X) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (fun f : C(X,ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g μ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [NNReal.coe_one,one_mul,dist_eq_norm,← integral_sub hf hg]
  calc
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, dist f g ∂μ := integral_mono (hf.sub hg).norm (integrable_const _) (fun x => by
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist x (f := f) (g := g))
    _ = dist f g := by simp

lemma bounded_dual_improvement {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    (o : X) (a b : C_c(X,ℝ)) (hab : marginalSum (a,b) ≤ quadraticCost 1) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      ‖φ‖ ≤ (R:ℝ)^2 ∧ ‖ψ‖ ≤ (R:ℝ)^2 ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∫ x, a x ∂μ)+(∫ y, b y ∂ν) ≤ (∫ x, φ x ∂μ)+(∫ y, ψ y ∂ν) := by
  have hb : ∀ y, -‖b.toContinuousMap‖ ≤ -b y := fun y => by
    have H := b.toContinuousMap.norm_coe_le_norm y
    exact neg_le_neg (le_abs_self _ |>.trans H)
  let v := hopfLax (fun y => -b y) 1
  have hvL : LipschitzWith R v := hopfLax_lipschitz_diameter hR b.continuous.neg hb
  let φ : C(X,ℝ) := ⟨fun x => v x-v o,hvL.continuous.sub continuous_const⟩
  have hφL : LipschitzWith R φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (v x-v o) (v y-v o) ≤ (R:ℝ)*dist x y
    simpa only [dist_sub_right] using hvL.dist_le_mul x y
  have hφabs (x : X) : |φ x| ≤ (R:ℝ)^2 := by
    have H := hvL.dist_le_mul x o
    change |v x-v o| ≤ _
    rw [Real.dist_eq] at H
    exact H.trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hR x o) R.coe_nonneg)
  have hφnorm : ‖φ‖ ≤ (R:ℝ)^2 := (ContinuousMap.norm_le φ (sq_nonneg _)).mpr hφabs
  have hφlower : ∀ x, -(R:ℝ)^2 ≤ -φ x := fun x => neg_le_neg (le_abs_self _ |>.trans (hφabs x))
  let w := hopfLax (fun x => -φ x) 1
  have hwL : LipschitzWith R w := hopfLax_lipschitz_diameter hR φ.continuous.neg hφlower
  let ψ : C(X,ℝ) := ⟨w,hwL.continuous⟩
  have hψabs (y : X) : |ψ y| ≤ (R:ℝ)^2 := by
    apply abs_le.mpr
    constructor
    · exact lower_le_hopfLax hφlower (by norm_num : (0:ℝ)<1) y
    · have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y o
      have HR := hR y o
      change hopfLax _ _ _ ≤ _
      have hφo : φ o = 0 := sub_self _
      dsimp only [hopfObjective] at H
      rw [hφo] at H
      nlinarith [sq_le_sq₀ dist_nonneg R.coe_nonneg |>.mpr HR,sq_nonneg (R:ℝ)]
  refine ⟨φ,ψ,hφL,hwL,hφnorm,(ContinuousMap.norm_le ψ (sq_nonneg _)).mpr hψabs,?_,?_⟩
  · intro x y
    have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y x
    change φ x+w y ≤ _
    dsimp [w,hopfObjective] at *
    rw [dist_comm y x] at H
    linarith
  · intro μ ν _ _
    have haφ (x : X) : a x ≤ φ x+v o := by
      suffices a x ≤ v x by dsimp [φ]; linarith
      apply le_csInf ⟨hopfObjective (fun y => -b y) 1 x x,mem_range_self x⟩
      rintro r ⟨y,rfl⟩
      have H := hab (x,y)
      change a x+b y ≤ dist x y^2/(2*1) at H
      dsimp [hopfObjective]
      linarith
    have hbψ (y : X) : b y ≤ ψ y-v o := by
      suffices b y+v o ≤ w y by change b y ≤ w y-v o; linarith
      apply le_csInf ⟨hopfObjective (fun x => -φ x) 1 y y,mem_range_self y⟩
      rintro r ⟨x,rfl⟩
      have H := hopfLax_le_objective hb (by norm_num : (0:ℝ)<1) x y
      change v x ≤ -b y+dist x y^2/(2*1) at H
      dsimp [hopfObjective,φ]
      rw [dist_comm y x]
      linarith
    have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hψi : Integrable ψ ν := ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have H := integral_mono a.integrable (hφi.add (integrable_const _)) haφ
    have I := integral_mono b.integrable (hψi.sub (integrable_const _)) hbψ
    change (∫ x,a x ∂μ) ≤ ∫ x,φ x+v o ∂μ at H
    change (∫ x,b x ∂ν) ≤ ∫ x,ψ x-v o ∂ν at I
    rw [integral_add hφi (integrable_const _),integral_const] at H
    rw [integral_sub hψi (integrable_const _),integral_const] at I
    simp only [probReal_univ,one_smul] at H I
    linarith

lemma compact_kantorovich_potentials (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R : ℝ≥0}
    (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×X), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, quadraticCost 1 p ∂q) ≤ ∫ p, quadraticCost 1 p ∂q') ∧
      ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
        (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
        ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  obtain ⟨q,hqp,hq0,hq1,hqmin,hqdual⟩ := compact_kantorovich_duality μ ν (quadraticCost 1)
  let _ := hqp
  let K := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ (R:ℝ)^2}
  let A := {p : C(X,ℝ)×C(X,ℝ) | ∀ x y, p.1 x+p.2 y ≤ dist x y^2/2}
  let S := (K×ˢK) ∩ A
  have hK : IsCompact K := isCompact_lipschitz_norm_ball R (sq_nonneg _)
  have hA : IsClosed A := by
    simp only [A,ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_le ((continuous_eval_const x).comp continuous_fst |>.add
      ((continuous_eval_const y).comp continuous_snd)) continuous_const
  have hS : IsCompact S := (hK.prod hK).inter_right hA
  have happrox (ε : ℝ) (hε : 0 < ε) : ∃ p ∈ S,
      (∫ z,quadraticCost 1 z ∂q) < (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)+ε := by
    obtain ⟨⟨a,b⟩,hab,hεab⟩ := hqdual ε hε
    obtain ⟨φ,ψ,hφL,hψL,hφB,hψB,hφψ,hI⟩ := bounded_dual_improvement hR o a b hab
    refine ⟨(φ,ψ),⟨⟨⟨hφL,hφB⟩,⟨hψL,hψB⟩⟩,hφψ⟩,?_⟩
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν)+ε
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,a x ∂μ)+(∫ y,b y ∂ν)+ε at hεab
    have HH := hI μ ν
    linarith
  have hSne : S.Nonempty := by obtain ⟨p,hp,_⟩ := happrox 1 (by norm_num); exact ⟨p,hp⟩
  let I : C(X,ℝ)×C(X,ℝ) → ℝ := fun p => (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)
  have hI : Continuous I := ((potential_integral_lipschitz μ).continuous.comp continuous_fst).add
    ((potential_integral_lipschitz ν).continuous.comp continuous_snd)
  obtain ⟨p,hp,hmax⟩ := hS.exists_isMaxOn hSne hI.continuousOn
  have hge : (∫ z,quadraticCost 1 z ∂q) ≤ I p := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨r,hr,hir⟩ := happrox ε hε
    have HH := hmax hr
    change (∫ x,r.1 x ∂μ)+(∫ y,r.2 y ∂ν) ≤ I p at HH
    linarith
  let φ : C_c(X,ℝ) := ⟨p.1,HasCompactSupport.of_compactSpace _⟩
  let ψ : C_c(X,ℝ) := ⟨p.2,HasCompactSupport.of_compactSpace _⟩
  have hsum : (∫ z,marginalSum (φ,ψ) z ∂q) = I p :=
    integral_marginalSum_of_marginals μ ν hq0 hq1 (φ,ψ)
  have hle : marginalSum (φ,ψ) ≤ quadraticCost 1 := by
    intro z
    simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using hp.2 z.1 z.2
  have heq : ∀ᵐ z ∂q,marginalSum (φ,ψ) z = quadraticCost 1 z := by
    apply (integral_eq_iff_of_ae_le (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable
      (ae_of_all _ hle)).mp
    apply le_antisymm (integral_mono (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable hle)
    rw [hsum]
    exact hge
  refine ⟨q,hqp,hq0,hq1,hqmin,p.1,p.2,hp.1.1.1,hp.1.2.1,hp.2,?_⟩
  simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using heq

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_SquareControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.squareControl {γ : Curve X} (h : IsGeodesic γ) :
    IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
  refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
  intro s t hst
  rw [h s t,intervalIntegral.integral_const,smul_eq_mul,
    abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr hst)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.integrable_length_sq {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  apply (integrable_const ((2*R)^2)).mono'
    (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).pow 2).aestronglyMeasurable
  filter_upwards [hb] with γ hγ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mpr
  have H := dist_triangle (γ timeZero) o (γ timeOne)
  rw [dist_comm o] at H
  linarith [hγ timeZero,hγ timeOne]

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_IntegrableEvalBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma BoundedTracks.integrable_lipschitz_eval {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  obtain ⟨o,R,_hR,hb⟩ := hb
  apply (integrable_const (|f o|+L*R)).mono'
    (hf.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  filter_upwards [hb] with γ hγ
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs]
  have H := hf.dist_le_mul (γ t) o
  rw [Real.dist_eq] at H
  have J := abs_add_le (f (γ t)-f o) (f o)
  rw [sub_add_cancel] at J
  have T := mul_le_mul_of_nonneg_left (hγ t) L.coe_nonneg
  linarith

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile1
noncomputable section

noncomputable section
noncomputable section
namespace WeakHessianTransport
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma lowerLipExtension_bdd {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : X) :
    BddAbove (range (fun z : S => f z - D * dist x z)) := by
  obtain ⟨o⟩ := ‹Nonempty S›
  refine ⟨f o+D*dist x o,?_⟩
  rintro r ⟨z,rfl⟩
  have H := hf.le_add_mul z o
  have J := mul_le_mul_of_nonneg_left (dist_triangle_left (z:X) (o:X) x) D.coe_nonneg
  change f z ≤ f o+D*dist (z:X) (o:X) at H
  nlinarith

lemma lowerLipExtension_eq {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : S) : lowerLipExtension S f D x = f x := by
  apply le_antisymm
  · apply ciSup_le
    intro z
    have H := hf.le_add_mul z x
    change f z ≤ f x+D*dist (z:X) (x:X) at H
    rw [dist_comm] at H
    linarith
  · have H := le_ciSup (lowerLipExtension_bdd hf (x:X)) x
    simpa only [dist_self,mul_zero,sub_zero,lowerLipExtension] using H

lemma lowerLipExtension_lipschitz {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) : LipschitzWith D (lowerLipExtension S f D) := by
  apply LipschitzWith.of_le_add_mul D
  intro x y
  apply ciSup_le
  intro z
  have H := le_ciSup (lowerLipExtension_bdd hf y) z
  change f z-D*dist y z ≤ lowerLipExtension S f D y at H
  have J := mul_le_mul_of_nonneg_left (dist_triangle y x (z:X)) D.coe_nonneg
  rw [dist_comm y x] at J
  linarith

lemma quadratic_cost_two_point_lower {D : ℝ≥0} {z w x y : X}
    (hD : dist z w ≤ D) :
    dist z w^2/2-D*(dist x z+dist y w) ≤ dist x y^2/2 := by
  have hr : 0 ≤ dist x z+dist y w := by positivity
  have ha : dist z w ≤ dist x z+dist y w+dist x y := by
    have H := dist_triangle z x w
    have J := dist_triangle x y w
    rw [dist_comm z x] at H
    linarith
  by_cases h : dist x y ≤ dist z w
  · have H : dist z w^2-dist x y^2 ≤ (dist x z+dist y w)*(2*D) := by
      calc
        _ = (dist z w-dist x y)*(dist z w+dist x y) := by ring
        _ ≤ (dist x z+dist y w)*(dist z w+dist x y) := by gcongr; linarith
        _ ≤ (dist x z+dist y w)*(2*D) := by gcongr; linarith
    nlinarith
  · have H := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (le_of_not_ge h)
    nlinarith [mul_nonneg D.coe_nonneg hr]

lemma lowerLipExtension_dual {S : Set X} [Nonempty S] {f g : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (hg : LipschitzWith D g)
    (hD : ∀ z w : S, dist (z:X) (w:X) ≤ D)
    (hdual : ∀ z w : S, f z+g w ≤ dist (z:X) (w:X)^2/2) (x y : X) :
    lowerLipExtension S f D x+lowerLipExtension S g D y ≤ dist x y^2/2 := by
  rw [← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hf x)).mpr
  intro z
  rw [le_sub_iff_add_le,add_comm,← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hg y)).mpr
  intro w
  have H := quadratic_cost_two_point_lower (hD z w) (x := x) (y := y)
  have J := hdual z w
  linarith

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
open WeakHessian

lemma quadraticTransportCost_map_subtype {S : Set X} (hS : MeasurableSet S)
    (q : Measure (S×S)) :
    QuadraticTransportCost (q.map (Prod.map Subtype.val Subtype.val)) =
      QuadraticTransportCost q := by
  unfold QuadraticTransportCost
  rw [lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2)
    ((MeasurableEmbedding.subtype_coe hS).prodMap
      (MeasurableEmbedding.subtype_coe hS)).measurable]
  rfl

lemma compact_quadraticCost_eq [CompactSpace X] (q : Measure (X×X))
    [IsFiniteMeasure q] :
    QuadraticTransportCost q = ENNReal.ofReal (2*(∫ p,quadraticCost 1 p ∂q)) := by
  have hi : Integrable (fun p : X×X => dist p.1 p.2^2) q :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ p : X×X, dist p.1 p.2^2 ∂q) = 2*(∫ p,quadraticCost 1 p ∂q) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by simp only [quadraticCost_apply]; ring)
  rw [← heq,ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => sq_nonneg _))]
  apply lintegral_congr
  intro p
  rw [edist_dist,ENNReal.ofReal_pow dist_nonneg]

lemma compact_kantorovich_potentials_of_optimal [CompactSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  have hqp : IsProbabilityMeasure q := by
    constructor
    have H := congrArg (fun μ => μ Set.univ) hq.1.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using H
  let := hqp
  obtain ⟨q',hqp',hq0',hq1',hqmin',φ,ψ,hφ,hψ,hdual,hcontact⟩ :=
    compact_kantorovich_potentials μ ν hR o
  let := hqp'
  have H := hq.2 q' ⟨hq0',hq1'⟩
  rw [compact_quadraticCost_eq,compact_quadraticCost_eq] at H
  have hcost : (∫ p,quadraticCost 1 p ∂q) ≤ ∫ p,quadraticCost 1 p ∂q' := by
    have hn : 0 ≤ 2*(∫ p,quadraticCost 1 p ∂q') := by
      apply mul_nonneg (by norm_num)
      apply integral_nonneg
      intro p
      simp only [quadraticCost_apply]
      positivity
    have he := (ENNReal.ofReal_le_ofReal_iff hn).mp H
    linarith
  have hm (r : Measure (X×X)) [IsProbabilityMeasure r]
      (hr0 : r.map Prod.fst = μ) (hr1 : r.map Prod.snd = ν) :
      (∫ p,φ p.1+ψ p.2 ∂r) = (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν) := by
    rw [integral_add,← integral_map measurable_fst.aemeasurable φ.continuous.aestronglyMeasurable,
      ← integral_map measurable_snd.aemeasurable ψ.continuous.aestronglyMeasurable,hr0,hr1]
    · exact (φ.continuous.comp continuous_fst).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (ψ.continuous.comp continuous_snd).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun p : X×X => φ p.1+ψ p.2) q :=
    ((φ.continuous.comp continuous_fst).add (ψ.continuous.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨φ,ψ,hφ,hψ,hdual,?_⟩
  have heq : (∫ p,φ p.1+ψ p.2 ∂q) = (∫ p,quadraticCost 1 p ∂q) := by
    apply le_antisymm
    · apply integral_mono hi (quadraticCost 1).integrable
      intro p
      simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2
    · calc
        _ ≤ ∫ p,quadraticCost 1 p ∂q' := hcost
        _ = ∫ p,φ p.1+ψ p.2 ∂q' := by
          apply integral_congr_ae
          filter_upwards [hcontact] with p hp
          simpa only [quadraticCost_apply,mul_one] using hp.symm
        _ = _ := by rw [hm q' hq0' hq1',hm q hq.1.1 hq.1.2]
  have H := (integral_eq_iff_of_ae_le hi (quadraticCost 1).integrable
    (ae_of_all _ (fun p => by simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2))).mp heq
  filter_upwards [H] with p hp
  simpa only [quadraticCost_apply,mul_one] using hp

lemma bounded_support_kantorovich_potentials
    {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ y ∂ν, y ∈ S)
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) :
    ∃ φ ψ : X → ℝ, LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q,φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : Nonempty S := hne.to_subtype
  have he := MeasurableEmbedding.subtype_coe hS.measurableSet
  have hep := he.prodMap he
  let μs : Measure S := μ.comap Subtype.val
  let νs : Measure S := ν.comap Subtype.val
  have hμr : ∀ᵐ x ∂μ,x ∈ range (Subtype.val : S → X) := by simpa using hμ
  have hνr : ∀ᵐ x ∂ν,x ∈ range (Subtype.val : S → X) := by simpa using hν
  let : IsProbabilityMeasure μs := he.isProbabilityMeasure_comap hμr
  let : IsProbabilityMeasure νs := he.isProbabilityMeasure_comap hνr
  have hμs : μs.map Subtype.val = μ := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hμr]
  have hνs : νs.map Subtype.val = ν := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hνr]
  have hqr : ∀ᵐ p ∂q,p ∈ range (Prod.map (Subtype.val : S → X) (Subtype.val : S → X)) := by
    have H : ∀ᵐ p ∂q,p.1 ∈ S := by
      apply (ae_map_iff measurable_fst.aemeasurable hS.measurableSet).mp
      rwa [hq.1.1]
    have J : ∀ᵐ p ∂q,p.2 ∈ S := by
      apply (ae_map_iff measurable_snd.aemeasurable hS.measurableSet).mp
      rwa [hq.1.2]
    filter_upwards [H,J] with p hp0 hp1
    exact ⟨(⟨p.1,hp0⟩,⟨p.2,hp1⟩),rfl⟩
  let qs : Measure (S×S) := q.comap (Prod.map Subtype.val Subtype.val)
  have hqs : qs.map (Prod.map Subtype.val Subtype.val) = q := by
    rw [hep.map_comap,Measure.restrict_eq_self_of_ae_mem hqr]
  have hqs0 : qs.map Prod.fst = μs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_fst,hμs,← hq.1.1,← hqs,
      Measure.map_map measurable_fst hep.measurable]
    rfl
  have hqs1 : qs.map Prod.snd = νs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_snd,hνs,← hq.1.2,← hqs,
      Measure.map_map measurable_snd hep.measurable]
    rfl
  have hqsopt : IsOptimalCoupling qs μs νs := by
    refine ⟨⟨hqs0,hqs1⟩,?_⟩
    intro r hr
    have hr' : IsCoupling (r.map (Prod.map Subtype.val Subtype.val)) μ ν := by
      constructor
      · rw [Measure.map_map measurable_fst hep.measurable,← hμs,← hr.1,
          Measure.map_map he.measurable measurable_fst]
        rfl
      · rw [Measure.map_map measurable_snd hep.measurable,← hνs,← hr.2,
          Measure.map_map he.measurable measurable_snd]
        rfl
    have H := hq.2 _ hr'
    rw [← hqs,quadraticTransportCost_map_subtype hS.measurableSet,
      quadraticTransportCost_map_subtype hS.measurableSet] at H
    exact H
  obtain ⟨f,g,hf,hg,hdual,hcontact⟩ := compact_kantorovich_potentials_of_optimal μs νs hqsopt
    (fun x y => hR x x.property y y.property) (Classical.arbitrary S)
  let φ := lowerLipExtension S f R
  let ψ := lowerLipExtension S g R
  refine ⟨φ,ψ,lowerLipExtension_lipschitz hf,lowerLipExtension_lipschitz hg,
    lowerLipExtension_dual hf hg (fun x y => hR x x.property y y.property) hdual,?_⟩
  rw [← hqs]
  apply (ae_map_iff hep.measurable.aemeasurable ?_).mpr
  · filter_upwards [hcontact] with p hp
    simpa only [Prod.map_fst,Prod.map_snd,φ,ψ,lowerLipExtension_eq hf,
      lowerLipExtension_eq hg,Subtype.dist_eq] using hp
  · exact (isClosed_eq
      (((lowerLipExtension_lipschitz hf).continuous.comp continuous_fst).add
        ((lowerLipExtension_lipschitz hg).continuous.comp continuous_snd))
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet

end WeakHessianTransport

end
end
end
end InlinedFile1

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_MulLogFenchel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

lemma mul_log_fenchel {r a : ℝ} (hr : 0 ≤ r) : r*a-Real.exp a+r ≤ r*Real.log r := by
  rcases hr.eq_or_lt with hr|hr
  · simp only [← hr,zero_mul,add_zero,sub_nonpos]
    exact (Real.exp_pos _).le
  · have H := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos a) hr)
    rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at H
    have := (mul_le_mul_of_nonneg_left H hr.le)
    simp only [mul_sub,mul_div_cancel₀ _ hr.ne',mul_one] at this
    nlinarith

lemma mul_log_floor_gap {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    r*Real.log r - (r*Real.log (max δ r)-max δ r+r) ≤ δ := by
  by_cases h : δ ≤ r
  · rw [max_eq_right h]
    linarith
  · have hrd : r ≤ δ := (le_of_not_ge h)
    rw [max_eq_left hrd]
    rcases hr.eq_or_lt with hr|hr
    · simp [← hr]
    · have H := mul_le_mul_of_nonneg_left (Real.log_le_log hr hrd) hr.le
      nlinarith

lemma exp_sub_bound {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    ‖Real.exp a-Real.exp b‖ ≤ Real.exp M*‖a-b‖ := by
  apply (convex_Iic M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_ hb ha
  intro x hx
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx

lemma min_sub_clamp {x a b : ℝ} (ha : a ≤ b) : ‖a-min x b‖ ≤ ‖a-x‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hx : x ≤ b
  · simp [min_eq_left hx]
  · rw [min_eq_right (le_of_not_ge hx),abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans (le_of_not_ge hx)))]
    linarith

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_fenchel (hμ : FiniteEntropy m μ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) + μ.real univ ≤ entropyReal m μ := by
  have hfμ : Integrable (fun x => f x) μ := f.integrable μ
  have hm : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have he : Integrable (fun x => Real.exp (f x)) m := by
    apply (integrable_const (Real.exp ‖f‖)).mono'
      (Real.continuous_exp.comp f.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (f.norm_coe_le_norm x))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono (hm.sub he |>.add hr) hlog (fun x => mul_log_fenchel ENNReal.toReal_nonneg)
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hm.sub he) hr,integral_sub hm he,integral_toReal_rnDeriv_mul hμ.1,
    Measure.integral_toReal_rnDeriv hμ.1,← entropyReal_eq_integral_density hμ.1] at H
  exact H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegrableExpBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_exp_of_bounded {f : X → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : ∀ x, f x ≤ A) (ν : Measure X) [IsFiniteMeasure ν] :
    Integrable (fun x => Real.exp (f x)) ν := by
  apply Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp A)
  exact ae_of_all _ fun x => by
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hA x)

lemma exists_continuous_fenchel_approx {f : X → ℝ} (hf : Measurable f) {A M : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hM : 0 < M) (hfM : ∀ x, f x ≤ Real.log M)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) ≤
        (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + ε := by
  let ν := μ+m
  have hfν : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hA)
  let η := ε/(1+M)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨h,hh,_⟩ := hfν.exists_boundedContinuous_integral_sub_le hη
  let g : X →ᵇ ℝ := h ⊓ BoundedContinuousFunction.const X (Real.log M)
  have hg (x : X) : g x = min (h x) (Real.log M) := rfl
  have hfg : Integrable (fun x => ‖f x-g x‖) ν := (hfν.sub (g.integrable ν)).norm
  have hL : (∫ x, ‖f x-g x‖ ∂ν) ≤ η := by
    apply le_trans (integral_mono hfg (hfν.sub (h.integrable ν)).norm ?_) hh
    intro x
    change ‖f x-g x‖ ≤ ‖f x-h x‖
    rw [hg]
    exact min_sub_clamp (hfM x)
  have hμν : μ ≤ ν := Measure.le_add_right le_rfl
  have hmν : m ≤ ν := Measure.le_add_left le_rfl
  have hfμ := hfν.mono_measure hμν
  have hμL : (∫ x, ‖f x-g x‖ ∂μ) ≤ η :=
    (integral_mono_measure hμν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hmL : (∫ x, ‖f x-g x‖ ∂m) ≤ η :=
    (integral_mono_measure hmν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hfirst : (∫ x, f x ∂μ) - (∫ x, g x ∂μ) ≤ η := by
    rw [← integral_sub hfμ (g.integrable μ)]
    exact (le_trans (Real.le_norm_self _) (norm_integral_le_integral_norm _)).trans hμL
  have hgM (x : X) : g x ≤ Real.log M := by rw [hg]; exact min_le_right _ _
  have heF := integrable_exp_of_bounded hf hfM m
  have heG := integrable_exp_of_bounded g.continuous.measurable hgM m
  have heDiff : (∫ x, Real.exp (g x) ∂m) - (∫ x, Real.exp (f x) ∂m) ≤ M*η := by
    calc
      _ = ∫ x, Real.exp (g x)-Real.exp (f x) ∂m := (integral_sub heG heF).symm
      _ ≤ ∫ x, M*‖f x-g x‖ ∂m := by
        apply integral_mono (heG.sub heF) ((hfg.mono_measure hmν).const_mul M)
        intro x
        have H := exp_sub_bound (hgM x) (hfM x)
        rw [Real.exp_log hM,norm_sub_rev (g x)] at H
        exact (le_trans (Real.le_norm_self _) H)
      _ = M*(∫ x, ‖f x-g x‖ ∂m) := integral_const_mul _ _
      _ ≤ M*η := mul_le_mul_of_nonneg_left hmL hM.le
  refine ⟨g,?_⟩
  have H : (1+M)*η = ε := mul_div_cancel₀ ε (by linarith : (1+M) ≠ 0)
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyRealContinuousSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      entropyReal m μ ≤ (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ + ε := by
  have hμ := finiteEntropy_of_bounded_density hB hd
  let C := max 1 B.toReal
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := ε/(4*(1+m.real univ))
  have hmnon : 0 ≤ m.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  let M := C+δ
  have hM : 0 < M := add_pos hC hδ
  let r := fun x => min (μ.rnDeriv m x).toReal C
  have hrnon (x : X) : 0 ≤ r x := le_min ENNReal.toReal_nonneg hC.le
  have hrC (x : X) : r x ≤ C := min_le_right _ _
  have hrEq : r =ᵐ[m] fun x => (μ.rnDeriv m x).toReal := by
    filter_upwards [rnDeriv_le_of_domination hd hμ.1] with x hx
    exact min_eq_left ((ENNReal.toReal_mono hB hx).trans (le_max_right _ _))
  let f := fun x => Real.log (max δ (r x))
  have hf : Measurable f := Real.measurable_log.comp
    (measurable_const.max ((Measure.measurable_rnDeriv μ m).ennreal_toReal.min measurable_const))
  have htpos (x : X) : 0 < max δ (r x) := lt_of_lt_of_le hδ (le_max_left _ _)
  have hflo (x : X) : Real.log δ ≤ f x :=
    Real.log_le_log hδ (le_max_left _ _)
  have hfM (x : X) : f x ≤ Real.log M :=
    Real.log_le_log (htpos x) (max_le (by dsimp [M]; linarith) (by dsimp [M]; linarith [hrC x]))
  let A := |Real.log δ|+|Real.log M|
  have hfA (x : X) : ‖f x‖ ≤ A := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [A]
      have H := neg_abs_le (Real.log δ)
      linarith [hflo x,abs_nonneg (Real.log M)]
    · dsimp [A]
      have H := le_abs_self (Real.log M)
      linarith [hfM x,abs_nonneg (Real.log δ)]
  have hfμ : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have hfm : Integrable f m := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have he := integrable_exp_of_bounded hf hfM m
  have hrf : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have hpoint : ∀ᵐ x ∂m, (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal+δ := by
    filter_upwards [hrEq] with x hx
    have H := mul_log_floor_gap (r := (μ.rnDeriv m x).toReal) ENNReal.toReal_nonneg hδ
    have hfexp : Real.exp (f x) = max δ (μ.rnDeriv m x).toReal := by
      dsimp [f]
      rw [Real.exp_log (htpos x),hx]
    have hfeq : f x = Real.log (max δ (μ.rnDeriv m x).toReal) := by dsimp [f]; rw [hx]
    rw [hfexp,hfeq]
    linarith
  have H := integral_mono_ae hlog (((hrf.sub he).add hr).add (integrable_const δ)) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal)
      ((hrf.sub he).add hr) (integrable_const δ),
    integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hrf.sub he) hr,
    integral_sub hrf he,integral_toReal_rnDeriv_mul (f := f) hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1,integral_const,smul_eq_mul] at H
  obtain ⟨g,hg⟩ := exists_continuous_fenchel_approx (m := m) (μ := μ) hf hfA hM hfM (half_pos hε)
  refine ⟨g,?_⟩
  have hδeq : δ*(4*(1+m.real univ)) = ε := div_mul_cancel₀ ε (by positivity)
  have hδerr : m.real univ*δ ≤ ε/4 := by nlinarith
  linarith

lemma entropyReal_le_iff_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {a : ℝ} :
    entropyReal m μ ≤ a ↔ ∀ g : X →ᵇ ℝ,
      (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ ≤ a := by
  constructor
  · intro ha g
    exact (entropyReal_fenchel (finiteEntropy_of_bounded_density hB hd) g).trans ha
  · intro ha
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg⟩ := entropyReal_continuous_support hB hd hε
    exact hg.trans (by linarith [ha g])

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ClosedEntropyAlong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u v
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma isClosed_entropy_le_along {T : Type v} [TopologicalSpace T]
    (μ : T → ProbabilityMeasure X) (hμ : Continuous μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hd : ∀ t, (μ t:Measure X) ≤ B • m)
    (a : T → ℝ) (ha : Continuous a) :
    IsClosed {t | entropyReal m (μ t:Measure X) ≤ a t} := by
  have he : {t | entropyReal m (μ t:Measure X) ≤ a t} =
      ⋂ g : X →ᵇ ℝ, {t | (∫ x, g x ∂(μ t:Measure X))-(∫ x, Real.exp (g x) ∂m)+1 ≤ a t} := by
    ext t
    simp only [mem_ofPred_eq,mem_iInter]
    have H := entropyReal_le_iff_continuous_support hB (hd t) (a := a t)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using H
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_le ?_ ha
  exact (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hμ).sub continuous_const).add continuous_const

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientNormTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_norm_tendsto_of_sq_upper {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, ‖Dn n‖^2 ≤ ‖D‖^2+ε n) :
    Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    filter_upwards [hf.eventually
      ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dn n,hn n,hle⟩)
  · intro b hb
    have hbpos : 0 < b := lt_of_le_of_lt (norm_nonneg D) hb
    have hgap : 0 < b^2-‖D‖^2 := by nlinarith [norm_nonneg D]
    filter_upwards [hε.eventually (gt_mem_nhds hgap)] with n hn'
    nlinarith [hbound n, norm_nonneg (Dn n)]

lemma exists_lipschitz_strong_slopes (hfinite : FiniteOnBoundedSets m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ hDs : ∀ n, MemLp (fun x => (localSlope (fs n) x).toReal) 2 m,
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
        Tendsto (fun n => (hDs n).toLp (fun x => (localSlope (fs n) x).toReal))
          atTop (𝓝 D) := by
  have hex (n : ℕ) := cheegerEnergy_lt_approx (f := f)
    (a := ENNReal.ofReal (‖D‖^2/2+1/((n:ℝ)+1)))
    (by rw [henergy]; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (lt_add_of_pos_right _ (by positivity)))
    (ε := 1/((n:ℝ)+1)) (by positivity)
  choose fs hLip hfs hdist hEn using hex
  have hfin (n : ℕ) : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) : MemLp (fun x => (localSlope (fs n) x).toReal) 2 m :=
    memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  have hfn : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hDn (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) := by
    exact (localSlope_isLocalWeakUpperGradient hfinite (hLip n).choose_spec).congr_ae
      (hfs n).coeFn_toLp.symm (hDs n).coeFn_toLp.symm
  have hbound (n : ℕ) : ‖Dn n‖^2 ≤ ‖D‖^2 + 2*(1/((n:ℝ)+1)) := by
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' : ‖Dn n‖^2/2 < ‖D‖^2/2+1/((n:ℝ)+1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    linarith
  refine ⟨fs,hLip,hfs,hDs,hfn,?_⟩
  apply hD.tendsto_of_norm_tendsto hDn hfn
  exact upperGradient_norm_tendsto_of_sq_upper hDn hfn (fun _ hE => hD.norm_le hE)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))) hbound

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_OptimalPlansShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

lemma optimalPlansShort_of_ball {μ₀ μ₁ : Measure X} (o : X) (R : ℝ≥0)
    (hb₀ : μ₀ (Metric.closedBall o R)ᶜ = 0) (hb₁ : μ₁ (Metric.closedBall o R)ᶜ = 0) :
    OptimalPlansShort μ₀ μ₁ (2*R) := by
  intro π hp hg hopt
  let := hp
  let : IsProbabilityMeasure μ₀ := by rw [← hopt.1.interpolation_endpoints.1]; exact interpolation_probability π _
  let : IsProbabilityMeasure μ₁ := by rw [← hopt.1.interpolation_endpoints.2]; exact interpolation_probability π _
  have H := optimalPlan_supported_tube (μ₀ := ⟨μ₀,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩) (μ₁ := ⟨μ₁,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩)
    (⟨π,hp⟩ : ProbabilityMeasure (Curve X)) hg hopt.1 hb₀ hb₁
  exact (ae_iff.mpr H).mono fun _ h => boundedEndpointTube_length_le h

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

lemma optimal_planEnergy_eq {μ₀ μ₁ : Measure X} {π η : Measure (Curve X)}
    (hπ : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling η) μ₀ μ₁)
    (hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π)
    (hIη : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) η) :
    planEnergy π = planEnergy η := by
  apply (ENNReal.ofReal_eq_ofReal_iff (planEnergy_nonneg π) (planEnergy_nonneg η)).mp
  rw [← planCost_eq_ofReal_energy hIπ,← planCost_eq_ofReal_energy hIη]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

omit [BorelSpace X] [SecondCountableTopology X] in
lemma uniformCap_finite (c : EntropyCell m K N) : c.uniformCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_uniformCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.uniformCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) (compressionRate_nonneg (K:=K) env.dimension)) c.length.property))
  simpa only [uniformCap, mul_one] using mul_le_mul' (le_refl c.cap) H

end EntropyCell

namespace CellPlan
lemma energy_eq {c : EntropyCell m K N} (p q : CellPlan c) :
    planEnergy (p.law:Measure (Curve X)) = planEnergy (q.law:Measure (Curve X)) :=
  optimal_planEnergy_eq p.optimal q.optimal p.integrable_energy q.integrable_energy
end CellPlan

variable [ProperSpace X] [SigmaFinite m]

omit [SigmaFinite m]

namespace CellMidpoint
variable {c : EntropyCell m K N}

lemma left_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.leftCell env).uniformCap = c.uniformCap := by
  change (c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length)))*
    ENNReal.ofReal (Real.exp (2*compressionRate K N*((c.length:ℝ)/2))) = _
  rw [mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  congr 1
  ring

lemma right_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.rightCell env).uniformCap = c.uniformCap := p.left_uniformCap env

end CellMidpoint
end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_Join
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CellMidpoint
variable {c : EntropyCell m K N} (p : CellMidpoint c) (env : CDEnvironment m K N)

lemma left_energy (l : CellPlan (p.leftCell env)) :
    planEnergy (l.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let r := (env.midpoint (p.rightCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.1
  change ((p.join env l r).law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) at H
  rw [← H,planEnergy_half (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

lemma right_energy (r : CellPlan (p.rightCell env)) :
    planEnergy (r.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let l := (env.midpoint (p.leftCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.2
  change ((p.join env l r).law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) at H
  rw [← H,planEnergy_right (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

end CellMidpoint

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma build_dominated (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build n c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      exact dominated_mono_constant c.left_dominated (c.cap_le_uniformCap env)
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      exact dominated_mono_constant c.right_dominated (c.cap_le_uniformCap env)
  | succ n ih =>
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,← (env.midpoint c).left_uniformCap env]
      exact ih _ s hs
    · rw [env.build_right,← (env.midpoint c).right_uniformCap env]
      exact ih _ s hs

lemma entropy_chord_half {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : 0 ≤ s) :
    (1-s)*A+s*M-K/2*(s*(1-s))*(E/4) ≤
      (1-s/2)*A+(s/2)*B-K/2*((s/2)*(1-s/2))*E := by
  calc
    _ ≤ (1-s)*A+s*((A+B)/2-K/8*E)-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM hs
      linarith only [H]
    _ = _ := by ring

lemma entropy_chord_right {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : s ≤ 1) :
    (1-s)*M+s*B-K/2*(s*(1-s))*(E/4) ≤
      (1-(s+1)/2)*A+((s+1)/2)*B-K/2*(((s+1)/2)*(1-(s+1)/2))*E := by
  calc
    _ ≤ (1-s)*((A+B)/2-K/8*E)+s*B-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hs)
      linarith only [H]
    _ = _ := by ring

lemma build_entropy_bound (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.build n c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.build n c).law:Measure (Curve X)) := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      simp only [timeZero,sub_zero,one_mul,zero_mul,mul_zero,add_zero,le_refl]
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      simp only [timeOne,sub_self,zero_mul,one_mul,zero_add,mul_zero,sub_zero,le_refl]
  | succ n ih =>
    have hE := (env.build (n+1) c).energy_eq (env.midpoint c).toCellPlan
    rw [hE]
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half]
      apply (ih ((env.midpoint c).leftCell env) s hs).trans
      rw [(env.midpoint c).left_energy env]
      exact entropy_chord_half (env.midpoint c).entropy_bound s.2.1
    · rw [env.build_right]
      apply (ih ((env.midpoint c).rightCell env) s hs).trans
      rw [(env.midpoint c).right_energy env]
      exact entropy_chord_right (env.midpoint c).entropy_bound s.2.2

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_time (π : ProbabilityMeasure (Curve X)) : Continuous (lawAt π) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (t : Time) : (∫ x, f x ∂(lawAt π t:Measure X)) = ∫ γ, f (γ t) ∂(π:Measure (Curve X)) :=
    integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t; exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  · intro t; exact ae_of_all _ fun γ => f.norm_coe_le_norm (γ t)
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun γ => f.continuous.comp γ.continuous

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [ProperSpace X] in
lemma IsGeodesic.speed_energy_le {γ : Curve X} (hγ : IsGeodesic γ) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)^2) := by
  calc
    _ ≤ ∫⁻ _t in Icc (0:ℝ) 1, (ENNReal.ofReal (dist (γ timeZero) (γ timeOne)))^2 := by
      apply lintegral_mono_ae
      exact hγ.squareControl.metricSpeed_le.mono fun t ht => pow_le_pow_left' ht 2
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        sub_zero,ENNReal.ofReal_one,mul_one,ENNReal.ofReal_pow dist_nonneg]

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t :=
  Classical.choose_spec (env.exists_stable_plan c) n t ht

lemma limitPlan_entropy_bound_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  rw [env.limitPlan_dyadic c n t ht,(env.limitPlan c).energy_eq (env.build n c)]
  exact env.build_entropy_bound n c t ht

lemma limitPlan_dominated_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  rw [env.limitPlan_dyadic c n t ht]
  exact env.build_dominated n c t ht

lemma limitPlan_dominated (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  have hnu : IsFiniteMeasure (c.uniformCap • m.restrict Q) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top c.uniformCap_finite.lt_top (measure_lt_top _ _)⟩
  let := hnu
  have hclosed : IsClosed {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} :=
    (isClosed_probability_dominated _).preimage (continuous_lawAt_time _)
  have hdyadic : (⋃ n, dyadicTimes n) ⊆ {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    have hd := env.limitPlan_dominated_dyadic c n s hn
    have hsupport : interpolation ((env.limitPlan c).law:Measure (Curve X)) s Qᶜ = 0 :=
      geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) s
    have H := Measure.restrict_mono_measure hd Q
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport),Measure.restrict_smul] at H
  have H : (lawAt (env.limitPlan c).law t:Measure X) ≤ c.uniformCap • m.restrict Q :=
    (closure_minimal hdyadic hclosed) (dense_dyadicTimes t)
  exact H.trans (smul_le_smul_left _ Measure.restrict_le_self)

lemma limitPlan_supported (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) t

lemma limitPlan_finite_entropy (c : EntropyCell m K N) (t : Time) :
    FiniteEntropy m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let : IsProbabilityMeasure (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) :=
    interpolation_probability _ _
  have hs : ∀ᵐ x ∂interpolation ((env.limitPlan c).law:Measure (Curve X)) t, x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c t)
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs).mp
  apply finiteEntropy_of_bounded_density c.uniformCap_finite
  have H := Measure.restrict_mono_measure (env.limitPlan_dominated c t) Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs,Measure.restrict_smul] at H

lemma limitPlan_boundedTracks (c : EntropyCell m K N) :
    BoundedTracks ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨c.center,3*(c.radius:ℝ)+1,by positivity,?_⟩
  have H := optimalPlan_supported_tube (env.limitPlan c).law (env.limitPlan c).geodesic
    (env.limitPlan c).optimal.1 c.left_supported c.right_supported
  filter_upwards [ae_iff.mpr H] with γ hγ
  intro t
  exact (boundedEndpointTube_range hγ t).trans (by linarith)

lemma limitPlan_isTestPlan (c : EntropyCell m K N) :
    IsTestPlan m ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),⟨c.uniformCap.toNNReal,?_⟩,?_,?_⟩
  · intro t
    rw [ENNReal.coe_toNNReal c.uniformCap_finite]
    exact env.limitPlan_dominated c t
  · exact (env.limitPlan c).geodesic.mono fun γ hγ => hγ.squareControl.isAC2
  · have hB : (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2
        ∂volume ∂((env.limitPlan c).law:Measure (Curve X))) ≤ ENNReal.ofReal ((c.length:ℝ)^2) := by
      calc
        _ ≤ ∫⁻ _γ, ENNReal.ofReal ((c.length:ℝ)^2) ∂((env.limitPlan c).law:Measure (Curve X)) := by
          apply lintegral_mono_ae
          filter_upwards [(env.limitPlan c).geodesic,
            c.short _ inferInstance (env.limitPlan c).geodesic (env.limitPlan c).optimal] with γ hγ hlen
          exact hγ.speed_energy_le.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ dist_nonneg hlen 2))
        _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
    exact hB.trans_lt ENNReal.ofReal_lt_top

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LimitPlanEntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_entropy_bound (c : EntropyCell m K N) (t : Time) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let p := (env.limitPlan c).law
  have hs (s : Time) : ∀ᵐ x ∂(lawAt p s:Measure X), x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c s)
  have hd (s : Time) : (lawAt p s:Measure X) ≤ c.uniformCap • m.restrict Q := by
    have H := Measure.restrict_mono_measure (env.limitPlan_dominated c s) Q
    change (lawAt p s:Measure X).restrict Q ≤ (c.uniformCap • m).restrict Q at H
    rwa [Measure.restrict_eq_self_of_ae_mem (hs s),Measure.restrict_smul] at H
  have he (s : Time) : entropyReal (m.restrict Q) (lawAt p s:Measure X) =
      entropyReal m (lawAt p s:Measure X) :=
    entropyReal_restrict_reference Metric.isClosed_closedBall.measurableSet
      (env.limitPlan_finite_entropy c s).1 (hs s)
  let a : Time → ℝ := fun s =>
      (1-(s:ℝ))*entropyReal m (c.leftLaw:Measure X)+(s:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((s:ℝ)*(1-(s:ℝ)))*planEnergy (p:Measure (Curve X))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : IsClosed {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    simp_rw [← he]
    exact isClosed_entropy_le_along (lawAt p) (continuous_lawAt_time p) c.uniformCap_finite hd a ha
  have hdy : (⋃ n, dyadicTimes n) ⊆ {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    exact env.limitPlan_entropy_bound_dyadic c n s hn
  exact (closure_minimal hdy hc) (dense_dyadicTimes t)

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropyBoundedSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable




























open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable













open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory InformationTheory
open scoped Topology


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology














namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma finiteEntropy_of_bounded_supported (hf : FiniteOnBoundedSets m)
    (μ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hd : (μ:Measure X) ≤ C • m) : FiniteEntropy m (μ:Measure X) := by
  let Q := Metric.closedBall o (R:ℝ)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hf Q Metric.isBounded_closedBall⟩
  have hs' : ∀ᵐ x ∂(μ:Measure X), x ∈ Q := ae_iff.mpr hs
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs').mp
  apply finiteEntropy_of_bounded_density hC
  have H := Measure.restrict_mono_measure hd Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs',Measure.restrict_smul] at H

theorem CurvatureDimension.exists_entropy_testPlan (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hf : FiniteOnBoundedSets m)
    (μ₀ μ₁ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hs₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (h₀ : (μ₀:Measure X) ≤ C • m) (h₁ : (μ₁:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), IsTestPlan m (π:Measure (Curve X)) ∧
      BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      (∀ t : Time, FiniteEntropy m (interpolation (π:Measure (Curve X)) t)) ∧
      (∀ t : Time,
        entropyReal m (interpolation (π:Measure (Curve X)) t) ≤
          (1-(t:ℝ))*entropyReal m (μ₀:Measure X) +
          (t:ℝ)*entropyReal m (μ₁:Measure X) -
          K/2*(t:ℝ)*(1-(t:ℝ))*planEnergy (π:Measure (Curve X))) ∧
      (∀ t : Time, interpolation (π:Measure (Curve X)) t ≤
        (C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R))) • m) := by
  let env : CDEnvironment m K N := ⟨hN,hCD,hf⟩
  let c : EntropyCell m K N := {
    leftLaw := μ₀, rightLaw := μ₁, center := o, radius := R, length := 2*R,
    cap := C, cap_pos := hC0, cap_finite := hCt,
    left_supported := hs₀, right_supported := hs₁,
    left_dominated := h₀, right_dominated := h₁,
    left_entropy := finiteEntropy_of_bounded_supported hf μ₀ o R hs₀ hCt h₀,
    right_entropy := finiteEntropy_of_bounded_supported hf μ₁ o R hs₁ hCt h₁,
    short := by simpa using optimalPlansShort_of_ball o R hs₀ hs₁ }
  refine ⟨(env.limitPlan c).law,env.limitPlan_isTestPlan c,env.limitPlan_boundedTracks c,
    (env.limitPlan c).geodesic,(env.limitPlan c).optimal,
    env.limitPlan_finite_entropy c,?_,?_⟩
  · intro t
    simpa only [c,mul_assoc] using env.limitPlan_entropy_bound c t
  · intro t
    have h := env.limitPlan_dominated c t
    have hcap : c.uniformCap = C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R)) := by
      dsimp only [EntropyCell.uniformCap,c]
      congr 3
      push_cast
      ring
    rwa [hcap] at h

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ZeroDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile3
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integral {n : Measure X} {w : X → ℝ} (hw : Measurable w) (f : X → ℝ) :
    (∫ x, f x ∂squareDensityMeasure n w) = ∫ x, w x^2*f x ∂n := by
  rw [squareDensityMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_mass {n : Measure X} {w : X → ℝ} (hw : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure n w)] : (∫ x, w x^2 ∂n) = 1 := by
  have H := squareDensity_integral (n := n) hw (fun _ => (1:ℝ))
  simpa using H.symm

end WeakHessian

end
end InlinedFile3

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropySlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile5
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_zero_outside {m : Measure X} {w : X → ℝ} (hw : Measurable w)
    {Q : Set X} (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    ∀ᵐ x ∂m, x ∉ Q → w x = 0 := by
  have H := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp hs
  filter_upwards [H] with x hx hnot
  have he : ENNReal.ofReal (w x^2) = 0 := not_not.mp (mt hx hnot)
  have H := ENNReal.ofReal_eq_zero.mp he
  nlinarith [sq_nonneg (w x)]

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_le_sqrt_integral_sq {m : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x,f x*g x ∂m) ≤ Real.sqrt (∫ x,f x^2 ∂m)*Real.sqrt (∫ x,g x^2 ∂m) := by
  have he : (∫ x,f x*g x ∂m) = ⟪hf.toLp f,hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he,← norm_toLp_sq_eq_integral hf,← norm_toLp_sq_eq_integral hg,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

end WeakHessian

end
end InlinedFile5

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_DensityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile8
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma integral_sq_sub_le {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, |f x^2-g x^2| ∂m) ≤ ‖hf.toLp f-hg.toLp g‖*‖hf.toLp f+hg.toLp g‖ := by
  have H := integral_mul_le_sqrt_integral_sq (hf.sub hg).norm (hf.add hg).norm
  simp only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,sq_abs] at H
  have hi : (∫ x,|f x^2-g x^2| ∂m) = ∫ x,|f x-g x| *|f x+g x| ∂m := by
    congr 1
    funext x
    rw [← abs_mul]
    congr 1
    ring
  rw [hi]
  have hs : (∫ x,(f x-g x)^2 ∂m) = ‖hf.toLp f-hg.toLp g‖^2 := by
    rw [← MemLp.toLp_sub hf hg]
    exact (norm_toLp_sq_eq_integral (hf.sub hg)).symm
  have ha : (∫ x,(f x+g x)^2 ∂m) = ‖hf.toLp f+hg.toLp g‖^2 := by
    rw [← MemLp.toLp_add hf hg]
    exact (norm_toLp_sq_eq_integral (hf.add hg)).symm
  simpa only [hs,ha,Real.sqrt_sq (norm_nonneg _)] using H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_L1_tendsto {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {w : X → ℝ}
    (hfs : ∀ i, MemLp (fs i) 2 m) (hw : MemLp w 2 m)
    (hF : Tendsto (fun i => (hfs i).toLp (fs i)) l (𝓝 (hw.toLp w))) :
    Tendsto (fun i => ∫ x, |fs i x^2-w x^2| ∂m) l (𝓝 0) := by
  have H := ((hF.sub (tendsto_const_nhds (x := hw.toLp w))).norm).mul ((hF.add (tendsto_const_nhds (x := hw.toLp w))).norm)
  simp only [sub_self,norm_zero,zero_mul] at H
  exact squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) (fun i => integral_sq_sub_le (hfs i) hw) H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_pairing_bound {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m) {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m)
    {M : ℝ} (hM : ∀ᵐ x ∂m, ‖φ x‖ ≤ M) :
    |(∫ x,φ x ∂squareDensityMeasure m f)-(∫ x,φ x ∂squareDensityMeasure m g)| ≤
      M*(∫ x,|f x^2-g x^2| ∂m) := by
  rw [squareDensity_integral hf,squareDensity_integral hg]
  have hi : Integrable (fun x => f x^2) m := hf2.integrable_sq
  have hj : Integrable (fun x => g x^2) m := hg2.integrable_sq
  have hif : Integrable (fun x => f x^2*φ x) m := by simpa only [mul_comm] using hi.bdd_mul hφ hM
  have hig : Integrable (fun x => g x^2*φ x) m := by simpa only [mul_comm] using hj.bdd_mul hφ hM
  rw [← integral_sub hif hig,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x,‖f x^2*φ x-g x^2*φ x‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ x,M*|f x^2-g x^2| ∂m := by
      apply integral_mono_ae (hif.sub hig).norm ((hi.sub hj).abs.const_mul M)
      filter_upwards [hM] with x hx
      simp only [Pi.sub_apply,← sub_mul,norm_mul,Real.norm_eq_abs] at *
      nlinarith [abs_nonneg (f x^2-g x^2)]
    _ = _ := integral_const_mul _ _

lemma squareDensity_tendsto_probability {fs : ℕ → X → ℝ} {w : X → ℝ}
    (hfm : ∀ n, Measurable (fs n)) (hwm : Measurable w)
    (hfs : ∀ n, MemLp (fs n) 2 m) (hw : MemLp w 2 m)
    (hP : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fs n)))
    (hW : IsProbabilityMeasure (squareDensityMeasure m w))
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.toLp w))) :
    Tendsto (β := ProbabilityMeasure X) (fun n => squareDensityProbability m (fs n) (hP n)) atTop
      (𝓝 (squareDensityProbability m w hW)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have H := (squareDensity_L1_tendsto hfs hw hF).const_mul ‖φ‖
  simp only [mul_zero] at H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ H
  intro n
  exact squareDensity_pairing_bound (hfm n) hwm (hfs n) hw φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => φ.norm_coe_le_norm x)
end WeakHessian

end
end InlinedFile8

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile9
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma LipschitzWith.integrable_supported_ball {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {μ : Measure X} [IsFiniteMeasure μ]
    (o : X) (R : ℝ≥0) (hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R) : Integrable φ μ := by
  apply Integrable.of_bound hφ.continuous.aestronglyMeasurable (‖φ o‖+(L:ℝ)*R)
  filter_upwards [hs] with x hx
  have H := hφ.dist_le_mul x o
  have hd : dist x o ≤ R := hx
  calc
    ‖φ x‖ ≤ ‖φ o‖+‖φ x-φ o‖ := by simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub (φ o) (φ x)
    _ ≤ _ := by rw [← dist_eq_norm]; exact add_le_add le_rfl (H.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg))

lemma squareDensity_pairing_bound_supported {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    [IsProbabilityMeasure (squareDensityMeasure m f)] [IsProbabilityMeasure (squareDensityMeasure m g)]
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (o : X) (R : ℝ≥0)
    (hsf : ∀ᵐ x ∂squareDensityMeasure m f, x ∈ Metric.closedBall o R)
    (hsg : ∀ᵐ x ∂squareDensityMeasure m g, x ∈ Metric.closedBall o R) :
    |(∫ x,φ x ∂squareDensityMeasure m f)-(∫ x,φ x ∂squareDensityMeasure m g)| ≤
      ((L:ℝ)*R)*(∫ x,|f x^2-g x^2| ∂m) := by
  let H : X → ℝ := (Metric.closedBall o R).indicator (fun x => φ x-φ o)
  have hHm : AEStronglyMeasurable H m :=
    (hφ.continuous.sub continuous_const).aestronglyMeasurable.indicator measurableSet_closedBall
  have hHb : ∀ x, ‖H x‖ ≤ (L:ℝ)*R := by
    intro x
    by_cases hx : x ∈ Metric.closedBall o R
    · rw [show H x = φ x-φ o from indicator_of_mem hx _]
      exact (hφ.dist_le_mul x o).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    · simp only [H,indicator_of_notMem hx,norm_zero]; positivity
  have hI := squareDensity_pairing_bound hf hg hf2 hg2 hHm (ae_of_all _ hHb)
  have he (u : X → ℝ) [IsProbabilityMeasure (squareDensityMeasure m u)]
      (hs : ∀ᵐ x ∂squareDensityMeasure m u, x ∈ Metric.closedBall o R) :
      (∫ x,H x ∂squareDensityMeasure m u) = (∫ x,φ x ∂squareDensityMeasure m u)-φ o := by
    calc
      _ = ∫ x,φ x-φ o ∂squareDensityMeasure m u := integral_congr_ae (hs.mono fun x hx => indicator_of_mem hx _)
      _ = _ := by rw [integral_sub (LipschitzWith.integrable_supported_ball hφ o R hs) (integrable_const _)]; simp
  rw [he f hsf,he g hsg] at hI
  simpa only [sub_sub_sub_cancel_right] using hI

lemma planEnergy_le_of_contact {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hbπ : BoundedTracks π) (hbη : BoundedTracks η)
    (_hiπ : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hdual : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h1 : interpolation π timeOne = interpolation η timeOne) :
    planEnergy π-planEnergy η ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂interpolation η timeZero)) := by
  have hmap (p : Measure (Curve X)) (s : Time) (f : X → ℝ) (hf : Continuous f) :
      (∫ γ,f (γ s) ∂p) = ∫ x,f x ∂interpolation p s :=
    (integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable).symm
  have hC : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    calc
      _ = ∫ γ,dist (γ timeZero) (γ timeOne)^2/2 ∂π := integral_congr_ae hcontact
      _ = _ := integral_div _ _
  have hB : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂η) ≤ planEnergy η/2 := by
    apply le_trans (integral_mono ((hbη.integrable_lipschitz_eval hφ timeZero).add
      (hbη.integrable_lipschitz_eval hψ timeOne)) (hiη.div_const 2) (fun γ => hdual _ _))
    exact le_of_eq (integral_div _ _)
  rw [integral_add (hbπ.integrable_lipschitz_eval hφ timeZero) (hbπ.integrable_lipschitz_eval hψ timeOne),
    hmap π timeZero φ hφ.continuous,hmap π timeOne ψ hψ.continuous,h1] at hC
  rw [integral_add (hbη.integrable_lipschitz_eval hφ timeZero) (hbη.integrable_lipschitz_eval hψ timeOne),
    hmap η timeZero φ hφ.continuous,hmap η timeOne ψ hψ.continuous] at hB
  linarith
end WeakHessian

end
end InlinedFile9

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_PotentialCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile15
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_lipschitz_locally_uniform_subsequence
    (o : X) (L : ℝ≥0) (fs : ℕ → X → ℝ) (hLip : ∀ n, LipschitzWith L (fs n))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |fs n o| ≤ B) :
    ∃ f : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧ LipschitzWith L f ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      ∀ k : ℕ, TendstoUniformlyOn (fun n => fs (s n)) f atTop
        (Metric.closedBall o (k:ℝ)) := by
  let Q (k : ℕ) := Metric.closedBall o (k:ℝ)
  let (k : ℕ) : CompactSpace (Q k) := isCompact_iff_compactSpace.mp (isCompact_closedBall o (k:ℝ))
  let vs (n k : ℕ) : C(Q k,ℝ) := ⟨fun x => fs n x,(hLip n).continuous.comp continuous_subtype_val⟩
  let M (k : ℕ) := B+(L:ℝ)*k
  let S (k : ℕ) := {f : C(Q k,ℝ) | LipschitzWith L f ∧ ‖f‖ ≤ M k}
  have hS (k : ℕ) : IsCompact (S k) :=
    WeakHessianTransport.isCompact_lipschitz_norm_ball L (by dsimp [M]; positivity)
  have hvs (n k : ℕ) : vs n k ∈ S k := by
    refine ⟨?_,?_⟩
    · change LipschitzWith L (fun x : Q k => fs n x)
      simpa only [mul_one,Function.comp_def] using (hLip n).comp (LipschitzWith.subtype_val (Q k))
    · apply (ContinuousMap.norm_le _ (by dsimp [M]; positivity)).mpr
      intro x
      have hl := (hLip n).dist_le_mul x o
      have hd : dist (x:X) o ≤ k := x.property
      have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
      change ‖fs n x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact H.trans (add_le_add (hb n) (by rw [← Real.dist_eq]; exact hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)))
  obtain ⟨F,hF,s,hs,ht⟩ := (isCompact_pi_infinite hS).tendsto_subseq (fun n => hvs n)
  have hk (k : ℕ) : Tendsto (fun n => vs (s n) k) atTop (𝓝 (F k)) :=
    (continuous_apply k).tendsto F |>.comp ht
  have hxk (k : ℕ) (x : Q k) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (F k x)) :=
    (continuous_eval_const x).tendsto (F k) |>.comp (hk k)
  have hex (x : X) : ∃ k : ℕ, x ∈ Q k := by
    obtain ⟨k,hk⟩ := exists_nat_ge (dist x o)
    exact ⟨k,hk⟩
  let k (x : X) := (hex x).choose
  let f (x : X) := F (k x) ⟨x,(hex x).choose_spec⟩
  have hp (x : X) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x)) := hxk (k x) _
  have he (j : ℕ) (x : Q j) : F j x = f x := tendsto_nhds_unique (hxk j x) (hp x)
  have hf : LipschitzWith L f := by
    apply isClosed_setOfPred_lipschitzWith L |>.mem_of_tendsto (tendsto_pi_nhds.mpr hp)
    exact Eventually.of_forall fun n => hLip (s n)
  refine ⟨f,s,hs,hf,hp,?_⟩
  intro j
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (hk j)) ε hε] with n hn x hx
  have H := ContinuousMap.dist_apply_le_dist (f := vs (s n) j) (g := F j) ⟨x,hx⟩
  change dist (fs (s n) x) (F j ⟨x,hx⟩) ≤ _ at H
  rw [he] at H
  simpa only [dist_comm] using H.trans_lt hn
end WeakHessian

end
end InlinedFile15

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_DualLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile21
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma lipschitz_integral_tendsto_supported {μ : Measure X} [IsFiniteMeasure μ]
    (o : X) (R : ℝ≥0) (hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {L : ℝ≥0}
    (hfs : ∀ n, LipschitzWith L (fs n)) {B : ℝ} (hb : ∀ n, |fs n o| ≤ B)
    (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x,fs n x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B+(L:ℝ)*R)
    (fun n => (hfs n).continuous.aestronglyMeasurable) (integrable_const _)
  · intro n
    filter_upwards [hs] with x hx
    rw [Real.norm_eq_abs]
    have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
      simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
    apply H.trans (add_le_add (hb n) _)
    rw [← Real.dist_eq]
    exact (hfs n).dist_le_mul x o |>.trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
  · exact ae_of_all _ ht

lemma squareDensity_varying_pairing_tendsto {m : Measure X}
    {vs : ℕ → X → ℝ} {w : X → ℝ}
    (hvm : ∀ n, Measurable (vs n)) (hwm : Measurable w)
    (hv : ∀ n, MemLp (vs n) 2 m) (hw : MemLp w 2 m)
    (hvp : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n)))
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hV : Tendsto (fun n => (hv n).toLp (vs n)) atTop (𝓝 (hw.toLp w)))
    (o : X) (R : ℝ≥0)
    (hvs : ∀ n, ∀ᵐ x ∂squareDensityMeasure m (vs n), x ∈ Metric.closedBall o R)
    (hws : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {L : ℝ≥0}
    (hfs : ∀ n, LipschitzWith L (fs n)) {B : ℝ} (hb : ∀ n, |fs n o| ≤ B)
    (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m (vs n)) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  let (n : ℕ) : IsProbabilityMeasure (squareDensityMeasure m (vs n)) := hvp n
  have hTV := squareDensity_L1_tendsto hv hw hV
  have hbound := hTV.const_mul ((L:ℝ)*R)
  simp only [mul_zero] at hbound
  have hdiff : Tendsto (fun n => (∫ x,fs n x ∂squareDensityMeasure m (vs n))-
      (∫ x,fs n x ∂squareDensityMeasure m w)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hbound
    intro n
    exact squareDensity_pairing_bound_supported (hvm n) hwm (hv n) hw (hfs n) o R (hvs n) hws
  have H := hdiff.add (lipschitz_integral_tendsto_supported o R hws hfs hb ht)
  simpa only [zero_add,sub_add_cancel] using H

lemma contact_integral_eq {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) {φ ψ : X → ℝ} {L T : ℝ≥0}
    (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ x,φ x ∂interpolation π timeZero)+(∫ y,ψ y ∂interpolation π timeOne) = planEnergy π/2 := by
  have he (f : X → ℝ) (hf : Continuous f) (s : Time) :
      (∫ x,f x ∂interpolation π s) = ∫ γ,f (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable
  rw [he φ hφ.continuous,he ψ hψ.continuous,← integral_add
    (hb.integrable_lipschitz_eval hφ timeZero) (hb.integrable_lipschitz_eval hψ timeOne)]
  rw [integral_congr_ae hc]
  exact integral_div _ _

lemma contact_of_integral_eq {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π)
    (hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hd : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (he : (∫ x,φ x ∂interpolation π timeZero)+(∫ y,ψ y ∂interpolation π timeOne) = planEnergy π/2) :
    ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 := by
  have hmap (f : X → ℝ) (hf : Continuous f) (s : Time) :
      (∫ x,f x ∂interpolation π s) = ∫ γ,f (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmap φ hφ.continuous,hmap ψ hψ.continuous,← integral_add
    (hb.integrable_lipschitz_eval hφ timeZero) (hb.integrable_lipschitz_eval hψ timeOne),
    show planEnergy π/2 = ∫ γ,dist (γ timeZero) (γ timeOne)^2/2 ∂π from (integral_div _ _).symm] at he
  exact (integral_eq_iff_of_ae_le
    ((hb.integrable_lipschitz_eval hφ timeZero).add (hb.integrable_lipschitz_eval hψ timeOne))
    (hi.div_const 2) (ae_of_all _ fun γ => hd _ _)).mp he

omit [MeasurableSpace X] [BorelSpace X] in
lemma centered_dual_bound {π : Measure (Curve X)} [IsProbabilityMeasure π]
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith L ψ)
    (o : X) (R : ℝ≥0) (hz : φ o = 0)
    (hd : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (hs : ∀ᵐ γ ∂π, γ timeZero ∈ Metric.closedBall o R ∧ γ timeOne ∈ Metric.closedBall o R) :
    |ψ o| ≤ 2*(L:ℝ)*R := by
  have hu : ψ o ≤ 0 := by simpa [hz] using hd o o
  obtain ⟨γ,hc,hs⟩ := (hc.and hs).exists
  have h1 : φ (γ timeZero) ≤ (L:ℝ)*R := by
    have H := (hφ.dist_le_mul (γ timeZero) o).trans (mul_le_mul_of_nonneg_left hs.1 L.coe_nonneg)
    rw [Real.dist_eq,hz,sub_zero] at H
    exact (le_abs_self _).trans H
  have h2 : ψ (γ timeOne) ≤ ψ o+(L:ℝ)*R := by
    have H := (hψ.dist_le_mul (γ timeOne) o).trans (mul_le_mul_of_nonneg_left hs.2 L.coe_nonneg)
    rw [Real.dist_eq] at H
    linarith [le_abs_self (ψ (γ timeOne)-ψ o)]
  rw [abs_of_nonpos hu]
  nlinarith [sq_nonneg (dist (γ timeZero) (γ timeOne))]

omit [MeasurableSpace X] [BorelSpace X] in
lemma exists_dual_subsequence [ProperSpace X]
    (o : X) {L : ℝ≥0} (fs gs : ℕ → X → ℝ)
    (hf : ∀ n, LipschitzWith L (fs n)) (hg : ∀ n, LipschitzWith L (gs n))
    {B : ℝ} (hB : 0 ≤ B) (hbf : ∀ n, |fs n o| ≤ B) (hbg : ∀ n, |gs n o| ≤ B)
    (hd : ∀ n x y,fs n x+gs n y ≤ dist x y^2/2) :
    ∃ f g : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧
      LipschitzWith L f ∧ LipschitzWith L g ∧
      |f o| ≤ B ∧ |g o| ≤ B ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      (∀ x, Tendsto (fun n => gs (s n) x) atTop (𝓝 (g x))) ∧
      ∀ x y,f x+g y ≤ dist x y^2/2 := by
  obtain ⟨f,s,hs,hfL,hfT,_⟩ := exists_lipschitz_locally_uniform_subsequence o L fs hf hB hbf
  obtain ⟨g,t,ht,hgL,hgT,_⟩ := exists_lipschitz_locally_uniform_subsequence o L (fun n => gs (s n))
    (fun n => hg (s n)) hB (fun n => hbg (s n))
  have hfT' (x : X) := (hfT x).comp ht.tendsto_atTop
  refine ⟨f,g,fun n => s (t n),hs.comp ht,hfL,hgL,?_,?_,hfT',hgT,?_⟩
  · exact le_of_tendsto (hfT' o |>.abs) (Eventually.of_forall fun n => hbf _)
  · exact le_of_tendsto (hgT o |>.abs) (Eventually.of_forall fun n => hbg _)
  · intro x y
    exact le_of_tendsto ((hfT' x).add (hgT y)) (Eventually.of_forall fun n => hd _ x y)
end WeakHessian

end
end InlinedFile21

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_ResolventEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_energy_le (u : E) : Q (hQ.resolvent u) ≤ Q u := by
  have H := hQ.resolvent_minimizes u u
  have hle : Q (hQ.resolvent u) ≤ proximalFunctional Q u (hQ.resolvent u) := le_add_right le_rfl
  simpa only [proximalFunctional, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, ENNReal.ofReal_zero, add_zero] using hle.trans H

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_FormLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile13
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.form_cauchySchwarz (u v : hQ.domain) :
    (hQ.form u v)^2 ≤ hQ.realEnergy u*hQ.realEnergy v :=
  hQ.realEnergy_quadratic.polar_cauchySchwarz u v

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_le {t : ℝ} (ht : 0 < t) (u : E) :
    Q ((hQ.scale ht).resolvent u) ≤ Q u := by
  have H := (hQ.scale ht).resolvent_energy_le u
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top).mp H

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    {ts : ι → ℝ} (hts : ∀ i, 0 < ts i) (hl : Tendsto ts l (𝓝 0)) (v : hQ.domain) :
    Tendsto (fun i => (Q ((hQ.scale (hts i)).resolvent v)).toReal) l (𝓝 (hQ.realEnergy v)) := by
  have hv := hQ.scaled_resolvent_tendsto hd hts hl (v:E)
  have H : Tendsto (fun i => Q ((hQ.scale (hts i)).resolvent v)) l (𝓝 (Q v)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hv (hQ.lowerSemicontinuous v a ha)
    · intro b hb
      exact Eventually.of_forall fun i => (hQ.scaled_resolvent_energy_le (hts i) v).trans_lt hb
  exact (ENNReal.continuousAt_toReal v.property.ne).tendsto.comp H

lemma ClosedQuadraticEnergy.scaled_resolvent_form_error_le (v : hQ.domain) {t : ℝ} (ht : 0 < t) :
    (Q ((v:E)-(hQ.scale ht).resolvent v)).toReal ≤
      hQ.realEnergy v-(Q ((hQ.scale ht).resolvent v)).toReal := by
  let r : E := (hQ.scale ht).resolvent v
  let A : E := t⁻¹ • (r-v)
  have hg : hQ.IsFormGenerator r A := (hQ.scaled_resolvent_iff ht v r).mp rfl
  let u : hQ.domain := ⟨r,hg.1⟩
  have he : t • A = r-v := by dsimp [A]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hp := hg.2 (v-u)
  have hi : 0 ≤ -⟪A,(v-u:E)⟫_ℝ := by
    change 0 ≤ -⟪A,(v:E)-r⟫_ℝ
    have H : (v:E)-r = -(t • A) := by rw [he]; abel
    rw [H,inner_neg_right,neg_neg,real_inner_smul_right,real_inner_self_eq_norm_sq]
    positivity
  change 0 ≤ -⟪A,((v-u : hQ.domain):E)⟫_ℝ at hi
  change 2*hQ.form u (v-u) = _ at hp
  have H := hQ.realEnergy_add u (v-u)
  rw [add_sub_cancel] at H
  change (Q ((v:E)-r)).toReal ≤ _
  change hQ.realEnergy (v-u) ≤ hQ.realEnergy v-hQ.realEnergy u
  linarith

lemma ClosedQuadraticEnergy.exists_formGenerator_approx
    (hd : hQ.domain.topologicalClosure = ⊤) (v : hQ.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ u A : E, hQ.IsFormGenerator u A ∧ (Q ((v:E)-u)).toReal < ε := by
  let t : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hl : Tendsto t atTop (𝓝 0) := by
    simpa only [t,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have H := (tendsto_const_nhds (x := hQ.realEnergy v)).sub (hQ.scaled_resolvent_energy_tendsto hd ht hl v)
  simp only [sub_self] at H
  obtain ⟨n,hn⟩ := (H.eventually_lt_const hε).exists
  refine ⟨(hQ.scale (ht n)).resolvent v,(t n)⁻¹ • ((hQ.scale (ht n)).resolvent v-v),
    (hQ.scaled_resolvent_iff (ht n) v _).mp rfl,?_⟩
  exact (hQ.scaled_resolvent_form_error_le v (ht n)).trans_lt hn

lemma ClosedQuadraticEnergy.form_tendsto_zero_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (hu : Tendsto (fun i => (us i:E)) l (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) (v : hQ.domain) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r,A,hg,hr⟩ := hQ.exists_formGenerator_approx hd v
    (show 0 < (ε/2)^2/(M+1) by positivity)
  let r' : hQ.domain := ⟨r,hg.1⟩
  have hrem (i : ι) : |hQ.form (us i) (v-r')| < ε/2 := by
    have H := hQ.form_cauchySchwarz (us i) (v-r')
    have hener : hQ.realEnergy (v-r') < (ε/2)^2/(M+1) := hr
    have hn := hQ.realEnergy_quadratic.nonneg (v-r')
    have H' := mul_le_mul_of_nonneg_right (hbound i) hn
    have hp : (M+1)*hQ.realEnergy (v-r') < (ε/2)^2 := by
      have hh := (lt_div_iff₀ (by linarith : (0:ℝ) < M+1)).mp hener
      nlinarith
    rw [abs_lt]
    constructor <;> nlinarith
  have he (i : ι) : hQ.form (us i) r' = -⟪A,(us i:E)⟫_ℝ/2 := by
    rw [hQ.form_comm]
    have H := hg.2 (us i)
    change 2*hQ.form r' (us i) = _ at H
    linarith
  have Hinner : Tendsto (fun i => hQ.form (us i) r') l (𝓝 0) := by
    simp_rw [he]
    simpa using ((tendsto_const_nhds (x := A)).inner (𝕜 := ℝ) hu).neg.div_const 2
  have Habs := Hinner.norm
  simp only [norm_zero,Real.norm_eq_abs] at Habs
  filter_upwards [Habs.eventually_lt_const (half_pos hε)] with i hi
  have H : hQ.form (us i) v = hQ.form (us i) (v-r')+hQ.form (us i) r' := by rw [map_sub]; ring
  rw [Real.dist_eq,sub_zero,H]
  exact (abs_add_le _ _).trans_lt (by linarith [hrem i])

lemma ClosedQuadraticEnergy.form_tendsto_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u v : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 (hQ.form u v)) := by
  have hsub : Tendsto (fun i => ((us i-u : hQ.domain):E)) l (𝓝 0) := by simpa using hu.sub_const (u:E)
  have he (i : ι) : hQ.realEnergy (us i-u) ≤ 2*M+2*hQ.realEnergy u := by
    have H := hQ.realEnergy_quadratic.parallelogram (us i) u
    have hn := hQ.realEnergy_quadratic.nonneg (us i+u)
    linarith [hbound i]
  have H := hQ.form_tendsto_zero_of_bounded_energy hd (fun i => us i-u) hsub
    (show 0 ≤ 2*M+2*hQ.realEnergy u from by have h := hQ.realEnergy_quadratic.nonneg u; positivity) he v
  simp only [map_sub,LinearMap.sub_apply] at H
  simpa using H.add_const (hQ.form u v)

lemma ClosedQuadraticEnergy.form_energy_sub_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M)
    (hener : Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i-u)) l (𝓝 0) := by
  have hf := hQ.form_tendsto_of_bounded_energy hd us u u hu hM hbound
  rw [hQ.form_self] at hf
  have he (i : ι) : hQ.realEnergy (us i-u) =
      hQ.realEnergy (us i)+hQ.realEnergy u-2*hQ.form (us i) u := by
    rw [← hQ.form_self (us i-u)]
    simp only [map_sub,LinearMap.sub_apply,hQ.form_self,hQ.form_comm u (us i)]
    ring
  simp_rw [he]
  simpa only [two_mul, sub_self] using
    (hener.add_const (hQ.realEnergy u)).sub (hf.const_mul 2)

end WeakHessianFunctional

end
end InlinedFile13

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_GammaLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile16
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma norm_gamma_lipschitz_le (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ} (hu : Sobolev m u)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ‖(memLp_gamma_lipschitz hfin hpar hu hφ).toLp (gamma m u φ)‖ ≤
      (L:ℝ)*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have H : ‖(memLp_gamma_lipschitz hfin hpar hu hφ).toLp (gamma m u φ)‖ ≤
      ‖(hu.2.2.const_mul (L:ℝ)).toLp (fun x => (L:ℝ)*weakGradient m u x)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_gamma_lipschitz hfin hpar hu hφ).coeFn_toLp,
      (hu.2.2.const_mul (L:ℝ)).coeFn_toLp,abs_gamma_lipschitz_le hfin hpar hu.2.1 hφ] with x hx hy hz
    rw [hx,hy,Real.norm_eq_abs,Real.norm_eq_abs]
    exact hz.trans (le_abs_self _)
  have he : (hu.2.2.const_mul (L:ℝ)).toLp (fun x => (L:ℝ)*weakGradient m u x) =
      (L:ℝ) • hu.2.2.toLp (weakGradient m u) := by
    exact MemLp.toLp_const_smul (L:ℝ) hu.2.2
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg] at H
  exact H

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma abs_integral_mul_le_L2_norm {a b : X → ℝ} (ha : MemLp a 2 m) (hb : MemLp b 2 m) :
    |∫ x,a x*b x ∂m| ≤ ‖ha.toLp a‖*‖hb.toLp b‖ := by
  have H : (∫ x,a x*b x ∂m) = ⟪ha.toLp a,hb.toLp b⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [H]
  exact abs_real_inner_le_norm _ _

lemma abs_weighted_gamma_lipschitz_le (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {a u φ : X → ℝ} (ha : MemLp a 2 m)
    (hu : Sobolev m u) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |∫ x,a x*gamma m u φ x ∂m| ≤
      (L:ℝ)*‖ha.toLp a‖*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have H := (abs_integral_mul_le_L2_norm ha (memLp_gamma_lipschitz hfin hpar hu hφ)).trans
    (mul_le_mul_of_nonneg_left (norm_gamma_lipschitz_le hfin hpar hu hφ) (norm_nonneg _))
  simpa only [mul_left_comm (‖ha.toLp a‖) (L:ℝ),mul_assoc] using H

lemma weighted_gamma_root_difference_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v φ : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |(∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m)| ≤
      (L:ℝ)*‖(hu.1.sub hv.1).toLp (fun x => u x-v x)‖*‖hu.2.2.toLp (weakGradient m u)‖+
      (L:ℝ)*‖hv.1.toLp v‖*‖(hu.sub hfin hv).2.2.toLp (weakGradient m (fun x => u x-v x))‖ := by
  let hsub := hu.sub hfin hv
  have h1 := hu.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h2 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hv hφ)
  have h3 := (hu.1.sub hv.1).integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h4 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hsub hφ)
  have he : (∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m) =
      (∫ x,(u x-v x)*gamma m u φ x ∂m)+(∫ x,v x*gamma m (fun y => u y-v y) φ x ∂m) := by
    change (∫ x,(u * gamma m u φ) x ∂m)-(∫ x,(v * gamma m v φ) x ∂m) =
      (∫ x,((u-v)*gamma m u φ) x ∂m)+(∫ x,(v*gamma m (fun y => u y-v y) φ) x ∂m)
    rw [← integral_sub h1 h2,← integral_add h3 h4]
    apply integral_congr_ae
    filter_upwards [gamma_sub_left hfin hpar hu.2.1 hv.2.1 (localSobolev_of_lipschitz hfin hφ)] with x hx
    simp only [Pi.mul_apply,Pi.sub_apply]
    rw [hx]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_weighted_gamma_lipschitz_le hfin hpar (hu.1.sub hv.1) hu hφ)
    (abs_weighted_gamma_lipschitz_le hfin hpar hv.1 hsub hφ))
end WeakHessian

end
end InlinedFile16

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RootApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile6
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

lemma rootClip_lipschitz (B : ℝ) : LipschitzWith 1 (rootClip B) :=
  (LipschitzWith.const_min LipschitzWith.id B).const_max 0
lemma rootClip_zero {B : ℝ} (hB : 0 ≤ B) : rootClip B 0 = 0 := by simp [rootClip,hB]
lemma rootClip_nonneg (B r : ℝ) : 0 ≤ rootClip B r := le_max_left _ _
lemma rootClip_le {B : ℝ} (hB : 0 ≤ B) (r : ℝ) : rootClip B r ≤ B :=
  max_le hB (min_le_left _ _)
lemma rootClip_eq {B r : ℝ} (hr : 0 ≤ r) (hB : r ≤ B) : rootClip B r = r := by
  simp only [rootClip,min_eq_right hB,max_eq_right hr]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma exists_clipped_cutoff_approx (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (henergy : cheegerEnergy m w = ENNReal.ofReal (‖hw.2.2.toLp (weakGradient m w)‖^2/2))
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχn : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (_hχc : HasCompactSupport χ)
    (hwχ : ∀ᵐ x ∂m, w x*χ x = w x)
    (hDχ : ∀ᵐ x ∂m, weakGradient m w x*χ x = weakGradient m w x)
    (hwD : ∀ᵐ x ∂m, w x*weakGradient m χ x = 0) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B) ∧
      (∀ n, tsupport (fs n) ⊆ tsupport χ) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n)) ∧
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  let W := hw.1.toLp w
  let D := hw.2.2.toLp (weakGradient m w)
  have hD : IsMinimalLocalWeakUpperGradient m (W: X → ℝ) D :=
    (weakGradient_isMinimal hw.2.1.2).congr_ae hw.1.coeFn_toLp.symm hw.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (W: X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp]
    exact henergy
  obtain ⟨gs,hgLip,hgs,hsl,hg,hs⟩ := exists_lipschitz_strong_slopes hfin hD he
  let cs (n : ℕ) := rootClip B ∘ gs n
  let hc (n : ℕ) : MemLp (cs n) 2 m := (rootClip_lipschitz B).comp_memLp (rootClip_zero hB) (hgs n)
  have hcLip (n : ℕ) : GloballyLipschitz (cs n) := ⟨_,(rootClip_lipschitz B).comp (hgLip n).choose_spec⟩
  have hcn (n : ℕ) (x : X) : 0 ≤ cs n x := rootClip_nonneg _ _
  have hcB (n : ℕ) (x : X) : |cs n x| ≤ B := by
    rw [abs_of_nonneg (hcn n x)]; exact rootClip_le hB _
  have hcW : (rootClip_lipschitz B).compLp (rootClip_zero hB) W = W := by
    apply Lp.ext
    filter_upwards [(rootClip_lipschitz B).coeFn_compLp (rootClip_zero hB) W,
      hw.1.coeFn_toLp,hwn,hwB] with x hx hwx hn hb
    rw [hx]
    change rootClip B (W x) = W x
    change W x = w x at hwx
    rw [hwx,rootClip_eq hn hb]
  have hcs : Tendsto (fun n => (hc n).toLp (cs n)) atTop (𝓝 W) := by
    have H := ((rootClip_lipschitz B).continuous_compLp (rootClip_zero hB)).tendsto W |>.comp hg
    rw [hcW] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply Lp.ext
    filter_upwards [(hc n).coeFn_toLp,
      (rootClip_lipschitz B).coeFn_compLp (rootClip_zero hB) ((hgs n).toLp (gs n)),
      (hgs n).coeFn_toLp] with x h1 h2 h3
    simp only [h1,h2,Function.comp_apply,h3,cs]
  let hχS := localSobolev_of_lipschitz hfin hχ
  have hχB : ∀ᵐ x ∂m, |χ x| ≤ 1 := ae_of_all _ fun x => by rw [abs_of_nonneg (hχn x)]; exact hχ1 x
  have hχDB : ∀ᵐ x ∂m, |weakGradient m χ x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) χ,weakGradient_le_lipschitz hfin hχ] with x hx hy
    rwa [abs_of_nonneg hx]
  let A := boundedMulLp hχ.continuous.aestronglyMeasurable hχB
  let T := boundedMulLp (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB
  have hAW : A W = W := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB W,hw.1.coeFn_toLp,hwχ] with x hx hy hz
    change A W x = W x
    change A W x = W x*χ x at hx
    change W x = w x at hy
    rw [hx,hy,hz]
  have hAD : A D = D := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB D,hw.2.2.coeFn_toLp,hDχ] with x hx hy hz
    change A D x = D x
    change A D x = D x*χ x at hx
    change D x = weakGradient m w x at hy
    rw [hx,hy,hz]
  have hTW : T W = 0 := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB W,
      hw.1.coeFn_toLp,hwD,Lp.coeFn_zero (α := X) (E := ℝ) (p := 2) (μ := m)] with x hx hy hz hzero
    change T W x = (0 : Lp ℝ 2 m) x
    change T W x = W x*weakGradient m χ x at hx
    change W x = w x at hy
    rw [hx,hy,hz,hzero]
    rfl
  let fs (n : ℕ) (x : X) := cs n x*χ x
  let hfs (n : ℕ) : MemLp (fs n) 2 m := memLp_mul_bounded (hc n) hχ.continuous.aestronglyMeasurable hχB
  let Ds (n : ℕ) (x : X) := χ x*(localSlope (gs n) x).toReal+cs n x*weakGradient m χ x
  let hDs (n : ℕ) : MemLp (Ds n) 2 m := by
    apply (show MemLp (fun x => χ x*(localSlope (gs n) x).toReal) 2 m from by
      simpa only [mul_comm] using memLp_mul_bounded (hsl n) hχ.continuous.aestronglyMeasurable hχB).add
      (memLp_mul_bounded (hc n) (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB)
  refine ⟨fs,fun n => ⟨_,lipschitz_mul_bounded (hcLip n).choose_spec hχ (hcB n)
    (fun x => by rw [abs_of_nonneg (hχn x)]; exact hχ1 x)⟩,
    fun n x => ⟨mul_nonneg (hcn n x) (hχn x),?_⟩,?_,hfs,Ds,hDs,?_,?_,?_⟩
  · exact (mul_le_of_le_one_right (hcn n x) (hχ1 x)).trans (rootClip_le hB _)
  · intro n
    exact tsupport_mul_subset_right
  · intro n
    have H := ((localSlope_isLocalWeakUpperGradient hfin (hgLip n).choose_spec).normalContraction
      (rootClip_lipschitz B)).mul_bounded (weakGradient_isMinimal hχS.2).1
      (fun o R _hR => (hc n).restrict _) hχ.continuous.measurable.aemeasurable hχB hχDB
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Ds,abs_of_nonneg (hχn x),abs_of_nonneg (hcn n x),cs]
  · have H := A.continuous.tendsto W |>.comp hcs
    rw [hAW] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply Lp.ext
    filter_upwards [(hfs n).coeFn_toLp,boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB ((hc n).toLp (cs n)),
      (hc n).coeFn_toLp] with x hx hy hz
    change (A ((hc n).toLp (cs n))) x = _ at hy
    simp only [Function.comp_apply,hx,hy,hz,fs]
  · have H := (A.continuous.tendsto D |>.comp hs).add (T.continuous.tendsto W |>.comp hcs)
    rw [hAD,hTW,add_zero] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply Lp.ext
    filter_upwards [(hDs n).coeFn_toLp,Lp.coeFn_add (A ((hsl n).toLp _)) (T ((hc n).toLp _)),
      boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB ((hsl n).toLp _),
      boundedMulLp_ae (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB ((hc n).toLp _),
      (hsl n).coeFn_toLp,(hc n).coeFn_toLp] with x hx hy h1 h2 h3 h4
    change (A ((hsl n).toLp _)) x = _ at h1
    change (T ((hc n).toLp _)) x = _ at h2
    simp only [Function.comp_apply,hx,hy,Pi.add_apply,h1,h2,h3,h4,Ds,mul_comm]

section

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma rootCutoff_lipschitz (o : X) (R : ℝ) : LipschitzWith 1 (rootCutoff o R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rootCutoff o R x) (rootCutoff o R y) ≤
        dist (R+2-dist x o) (R+2-dist y o) := by
      simpa only [NNReal.coe_one,one_mul,rootCutoff] using
        (rootClip_lipschitz 1).dist_le_mul (R+2-dist x o) (R+2-dist y o)
    _ = dist (dist x o) (dist y o) := dist_sub_left _ _ _
    _ ≤ 1*dist x y := by simpa using dist_dist_dist_le_left x y o

lemma rootCutoff_nonneg (o : X) (R : ℝ) (x : X) : 0 ≤ rootCutoff o R x := rootClip_nonneg _ _
lemma rootCutoff_le_one (o : X) (R : ℝ) (x : X) : rootCutoff o R x ≤ 1 := rootClip_le zero_le_one _
lemma rootCutoff_one {o : X} {R : ℝ} {x : X} (hx : x ∈ Metric.closedBall o R) :
    rootCutoff o R x = 1 := by
  have H : dist x o ≤ R := hx
  simp only [rootCutoff,rootClip,min_eq_left (by linarith : 1 ≤ R+2-dist x o),max_eq_right zero_le_one]
lemma rootCutoff_support (o : X) (R : ℝ) : tsupport (rootCutoff o R) ⊆ Metric.closedBall o (R+2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have H : R+2 < dist x o := lt_of_not_ge hh
  have he : rootCutoff o R x = 0 := by
    apply max_eq_left
    exact (min_le_right _ _).trans (by linarith)
  exact hx he

end

lemma cutoff_gradient_identities (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : LocalSobolev m w) {Q : Set X} (hQ : MeasurableSet Q)
    (hws : ∀ᵐ x ∂m, x ∉ Q → w x = 0)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχeq : ∀ x ∈ Q, χ x = 1) :
    (∀ᵐ x ∂m, w x*χ x = w x) ∧
    (∀ᵐ x ∂m, weakGradient m w x*χ x = weakGradient m w x) ∧
    (∀ᵐ x ∂m, w x*weakGradient m χ x = 0) := by
  have hzero : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  have hone : LocalSobolev m (fun _ : X => (1:ℝ)) := by simpa only [zero_add] using hzero.add_const hfin 1
  have hDz := weakGradient_locality hw hzero hQ.compl hws
  have hDc := weakGradient_locality (localSobolev_of_lipschitz hfin hχ) hone hQ (ae_of_all _ hχeq)
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hws] with x hx
    by_cases h : x ∈ Q
    · rw [hχeq x h,mul_one]
    · rw [hx h,zero_mul]
  · filter_upwards [hDz,weakGradient_const (m := m) 0] with x hx hz
    by_cases h : x ∈ Q
    · rw [hχeq x h,mul_one]
    · rw [hx h,hz,zero_mul]
  · filter_upwards [hws,hDc,weakGradient_const (m := m) 1] with x hwx hx hz
    by_cases h : x ∈ Q
    · rw [hx h,hz,mul_zero]
    · rw [hwx h,zero_mul]

variable [ProperSpace X]

theorem CurvatureDimension.compact_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (o : X) (R : ℝ≥0) (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B) ∧
      (∀ n, tsupport (fs n) ⊆ Metric.closedBall o ((R:ℝ)+2)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n)) ∧
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  obtain ⟨hwχ,hDχ,hwD⟩ := cutoff_gradient_identities hfin hw.2.1 measurableSet_closedBall hws
    (rootCutoff_lipschitz o R) (fun x hx => rootCutoff_one hx)
  obtain ⟨fs,hLip,hBnd,hs,hfs,Ds,hDs,hUG,hfsT,hDsT⟩ := exists_clipped_cutoff_approx hfin hw hB hwn hwB
    (hcd.global_cheegerEnergy_eq_weakGradient hfin o hw)
    (rootCutoff_lipschitz o R) (rootCutoff_nonneg o R) (rootCutoff_le_one o R)
    (isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (rootCutoff_support o R))
    hwχ hDχ hwD
  exact ⟨fs,hLip,hBnd,fun n => (hs n).trans (rootCutoff_support o R),hfs,Ds,hDs,hUG,hfsT,hDsT⟩
end WeakHessian

end
end InlinedFile6

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormalizedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile7
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_probability_of_norm {m : Measure X} {w : X → ℝ}
    (hw : MemLp w 2 m) (hnorm : ‖hw.toLp w‖ = 1) :
    IsProbabilityMeasure (squareDensityMeasure m w) := by
  constructor
  rw [squareDensityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mp hw) (ae_of_all _ fun x => sq_nonneg (w x)),
    ← norm_toLp_sq_eq_integral hw,hnorm,one_pow,ENNReal.ofReal_one]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma normalize_root_approx {w : X → ℝ} (hw : Sobolev m w)
    (hwnorm : ‖hw.1.toLp w‖ = 1) {B : ℝ} (_hB : 0 ≤ B)
    {Q : Set X} {fs : ℕ → X → ℝ} (hLip : ∀ n, GloballyLipschitz (fs n))
    (hb : ∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B)
    (hs : ∀ n, tsupport (fs n) ⊆ Q)
    (hfs : ∀ n, MemLp (fs n) 2 m)
    {Ds : ℕ → X → ℝ} (hDs : ∀ n, MemLp (Ds n) 2 m)
    (hUG : ∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n))
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)))
    (hD : Tendsto (fun n => (hDs n).toLp (Ds n)) atTop (𝓝 (hw.2.2.toLp (weakGradient m w)))) :
    ∃ vs : ℕ → X →ᵇ ℝ, (∀ n, GloballyLipschitz (vs n)) ∧
      (∀ n x, 0 ≤ vs n x ∧ vs n x ≤ 2*B) ∧
      (∀ n, tsupport (vs n) ⊆ Q) ∧
      ∃ hvs : ∀ n, MemLp (vs n) 2 m,
      (∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n))) ∧
      ∃ Es : ℕ → X → ℝ, ∃ hEs : ∀ n, MemLp (Es n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (vs n) (Es n)) ∧
        Tendsto (fun n => (hvs n).toLp (vs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hEs n).toLp (Es n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  have hn : Tendsto (fun n => ‖(hfs n).toLp (fs n)‖) atTop (𝓝 (1:ℝ)) := by
    simpa only [hwnorm] using hF.norm
  obtain ⟨k,hk⟩ := (eventually_atTop.1 (hn.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1))))
  let c (n : ℕ) := ‖(hfs (n+k)).toLp (fs (n+k))‖⁻¹
  have hcpos (n : ℕ) : 0 < c n := inv_pos.mpr (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n)))
  have hcle (n : ℕ) : c n ≤ 2 := by
    dsimp [c]
    apply (inv_le_comm₀ (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))) (by norm_num : (0:ℝ) < 2)).mpr
    simpa using (le_of_lt (hk _ (Nat.le_add_left k n)))
  have hc : Tendsto c atTop (𝓝 (1:ℝ)) := by
    simpa only [inv_one,Function.comp_apply,c] using (hn.comp (tendsto_add_atTop_nat k)).inv₀ one_ne_zero
  let vs (n : ℕ) : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => c n*fs (n+k) x) (continuous_const.mul (hLip (n+k)).choose_spec.continuous)
    (C := 2*B) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hcpos n).le (hb (n+k) x).1)]
      exact mul_le_mul (hcle n) (hb (n+k) x).2 (hb (n+k) x).1 (by norm_num))
  let hvs (n : ℕ) : MemLp (vs n) 2 m := (hfs (n+k)).const_mul (c n)
  have hveq (n : ℕ) : (hvs n).toLp (vs n) = c n • (hfs (n+k)).toLp (fs (n+k)) := by
    exact (hfs (n+k)).toLp_const_smul (c n)
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEeq (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) := by
    exact (hDs (n+k)).toLp_const_smul (c n)
  refine ⟨vs,fun n => (hLip (n+k)).const_mul (c n),fun n x => ⟨?_,?_⟩,?_,hvs,?_,Es,hEs,?_,?_,?_⟩
  · exact mul_nonneg (hcpos n).le (hb (n+k) x).1
  · exact mul_le_mul (hcle n) (hb (n+k) x).2 (hb (n+k) x).1 (by norm_num)
  · intro n
    exact tsupport_mul_subset_right.trans (hs (n+k))
  · intro n
    apply squareDensity_probability_of_norm (hvs n)
    rw [hveq,norm_smul,Real.norm_eq_abs,abs_of_pos (hcpos n)]
    exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))))
  · intro n
    simpa only [abs_of_pos (hcpos n),vs,Es,BoundedContinuousFunction.coe_ofNormedAddCommGroup] using (hUG (n+k)).const_mul (c n)
  · simp_rw [hveq]
    simpa only [one_smul,Function.comp_apply] using hc.smul (hF.comp (tendsto_add_atTop_nat k))
  · simp_rw [hEeq]
    simpa only [one_smul,Function.comp_apply] using hc.smul (hD.comp (tendsto_add_atTop_nat k))
variable [ProperSpace X]

theorem CurvatureDimension.normalized_compact_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (hwm : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (o : X) (R : ℝ≥0) (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0) :
    ∃ vs : ℕ → X →ᵇ ℝ, (∀ n, GloballyLipschitz (vs n)) ∧
      (∀ n x, 0 ≤ vs n x ∧ vs n x ≤ 2*B) ∧
      (∀ n, tsupport (vs n) ⊆ Metric.closedBall o ((R:ℝ)+2)) ∧
      ∃ hvs : ∀ n, MemLp (vs n) 2 m,
      (∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n))) ∧
      ∃ Es : ℕ → X → ℝ, ∃ hEs : ∀ n, MemLp (Es n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (vs n) (Es n)) ∧
        Tendsto (fun n => (hvs n).toLp (vs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hEs n).toLp (Es n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  have hnorm : ‖hw.1.toLp w‖ = 1 := by
    have H := norm_toLp_sq_eq_integral hw.1
    rw [squareDensity_mass hwm] at H
    nlinarith [norm_nonneg (hw.1.toLp w)]
  obtain ⟨fs,hLip,hb,hs,hfs,Ds,hDs,hUG,hF,hD⟩ :=
    hcd.compact_root_approximation hfin hw hB hwn hwB o R hws
  exact normalize_root_approx hw hnorm hB hLip hb hs hfs hDs hUG hF hD

end WeakHessian

end
end InlinedFile7

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile11
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]

lemma entropyReal_le_of_tendsto_supported (hfin : FiniteOnBoundedSets m)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (o : X) (R : ℝ≥0)
    (hss : ∀ n, ∀ᵐ x ∂(μs n:Measure X), x ∈ Metric.closedBall o R)
    (hs : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o R)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hds : ∀ n, (μs n:Measure X) ≤ C • m) (hd : (μ:Measure X) ≤ C • m)
    {a : ℕ → ℝ} {A : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hE : ∀ n, entropyReal m (μs n:Measure X) ≤ a n) : entropyReal m (μ:Measure X) ≤ A := by
  let Q := Metric.closedBall o (R:ℝ)
  have hQ : MeasurableSet Q := measurableSet_closedBall
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have dom (ν : ProbabilityMeasure X) (hsν : ∀ᵐ x ∂(ν:Measure X), x ∈ Q)
      (hdν : (ν:Measure X) ≤ C • m) : (ν:Measure X) ≤ C • m.restrict Q := by
    have H := Measure.restrict_mono_measure hdν Q
    rwa [Measure.restrict_eq_self_of_ae_mem hsν,Measure.restrict_smul] at H
  have ac (ν : ProbabilityMeasure X) (hdν : (ν:Measure X) ≤ C • m) : (ν:Measure X) ≪ m :=
    hdν.absolutelyContinuous.trans (Measure.AbsolutelyContinuous.rfl.smul_left _)
  rw [← entropyReal_restrict_reference hQ (ac μ hd) hs]
  apply (entropyReal_le_iff_continuous_support hC (dom μ hs hd)).mpr
  intro g
  have H : Tendsto (fun n => (∫ x,g x ∂(μs n:Measure X))-(∫ x,Real.exp (g x) ∂m.restrict Q)+1)
      atTop (𝓝 ((∫ x,g x ∂(μ:Measure X))-(∫ x,Real.exp (g x) ∂m.restrict Q)+1)) :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).tendsto μ |>.comp hμ).sub_const _ |>.add_const 1
  have J := le_of_tendsto_of_tendsto' H ha (fun n => by
    have HF := entropyReal_fenchel (finiteEntropy_of_bounded_density hC (dom (μs n) (hss n) (hds n))) g
    rw [entropyReal_restrict_reference hQ (ac (μs n) (hds n)) (hss n)] at HF
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using HF.trans (hE n))
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using J

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SigmaFinite m] in
lemma squareDensity_le_of_bound {w : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B) :
    squareDensityMeasure m w ≤ ENNReal.ofReal (B^2) • m := by
  rw [squareDensityMeasure,← withDensity_const]
  apply withDensity_mono
  filter_upwards [hwn,hwB] with x hx hy
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ hx hB).mpr hy)

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SigmaFinite m] in
lemma squareDensity_ae_support {w : X → ℝ} (hw : Measurable w) {Q : Set X}
    (hzero : ∀ᵐ x ∂m, x ∉ Q → w x = 0) :
    ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q := by
  apply (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mpr
  filter_upwards [hzero] with x hx hn
  by_contra h
  exact hn (by rw [hx h]; simp)
end WeakHessian

end
end InlinedFile11

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile18
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma toLp_tendsto_of_domination {fs : ℕ → X → ℝ} {f D : X → ℝ}
    (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m) (hD : MemLp D 2 m)
    (hb : ∀ n, ∀ᵐ x ∂m, ‖fs n x‖ ≤ ‖D x‖)
    (hT : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) := by
  have hi : UnifIntegrable fs 2 m := by
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := hD.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hd s hs hms)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ s
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  have ht : UnifTight fs 2 m := by
    intro ε hε
    obtain ⟨s,hsm,hs,hd⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num) hD).exists_measurableSet_indicator (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨s,hs.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hd n)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ sᶜ
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hfs f hf).mpr
    (tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hfs n).aestronglyMeasurable) hf hi ht hT)

omit [CompleteSpace X] in
lemma CurvatureDimension.integral_gamma_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {fs : ℕ → X → ℝ} {f g : X → ℝ}
    (hfs : ∀ n, Sobolev m (fs n)) (hf : Sobolev m f) (hg : Sobolev m g)
    (hT : Tendsto (fun n => (hfs n).1.toLp (fs n)) atTop (𝓝 (hf.1.toLp f)))
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ n, ‖(hfs n).2.2.toLp (weakGradient m (fs n))‖ ≤ M) :
    Tendsto (fun n => ∫ x,gamma m (fs n) g x ∂m) atTop (𝓝 (∫ x,gamma m f g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy hq
  let mk (v : X → ℝ) (hv : Sobolev m v) : Q.domain := ⟨hv.1.toLp v,by
    change cheegerEnergy m (hv.1.toLp v : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hv.1).mp hv⟩
  have he (v : X → ℝ) (hv : Sobolev m v) :
      Q.realEnergy (mk v hv) = ‖hv.2.2.toLp (weakGradient m v)‖^2/2 := by
    change (cheegerEnergy m (hv.1.toLp v : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hv,
      norm_toLp_sq_eq_integral hv.2.2]
  have hbE (n : ℕ) : Q.realEnergy (mk (fs n) (hfs n)) ≤ M^2/2 := by
    rw [he (fs n) (hfs n)]
    gcongr
    exact hb n
  have hpair (v : X → ℝ) (hv : Sobolev m v) :
      (∫ x,gamma m v g x ∂m) = 2*Q.form (mk v hv) (mk g hg) := by
    rw [← hcd.global_integral_gamma_form hfin o hq]
    apply integral_congr_ae
    exact gamma_congr_ae hv.1.coeFn_toLp.symm hg.1.coeFn_toLp.symm
  simp_rw [hpair f hf,hpair _ (hfs _)]
  exact (Q.form_tendsto_of_bounded_energy (cheeger_domain_dense hq)
    (fun n => mk (fs n) (hfs n)) (mk f hf) (mk g hg) hT
    (div_nonneg (pow_nonneg hM 2) (by norm_num) : 0 ≤ M^2/2) hbE).const_mul 2
end WeakHessian

end
end InlinedFile18

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SquareSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile17
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma Sobolev.square_bounded (hfin : FiniteOnBoundedSets m) {u : X → ℝ}
    (hu : Sobolev m u) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    Sobolev m (fun x => u x^2) := by
  have hsq : MemLp (fun x => u x^2) 2 m := by
    simpa only [pow_two] using memLp_mul_bounded hu.1 hu.1.aestronglyMeasurable hB
  have hc : ContDiff ℝ 1 (fun s : ℝ => s^2) := contDiff_id.pow 2
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  apply Sobolev.of_upperGradient hfin hsq
    ((weakGradient_isMinimal hu.2.1.2).1.comp_contDiff hu.1.aemeasurable hc hb)
  have hm : AEStronglyMeasurable (fun x => |deriv (fun s : ℝ => s^2) (u x)|) m := by
    simp only [hd]
    exact continuous_abs.comp_aestronglyMeasurable (hu.1.aestronglyMeasurable.const_mul 2)
  simpa only [mul_comm] using memLp_mul_bounded hu.2.2 hm (by simpa only [abs_abs] using hb)

lemma gamma_square_bounded (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v : X → ℝ}
    (hu : Sobolev m u) (hv : LocalSobolev m v) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    gamma m (fun x => u x^2) v =ᵐ[m] (fun x => 2*u x*gamma m u v x) := by
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  simpa only [Function.comp_def,id_eq,hd] using gamma_comp_contDiff hfin hpar hu.2.1 hv
    (contDiff_id.pow 2) (hu.square_bounded hfin hB).2.1.1 hb

lemma gamma_locality_left (hfin : FiniteOnBoundedSets m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∈ Q → f x = g x) :
    ∀ᵐ x ∂m, x ∈ Q → gamma m f v x = gamma m g v x := by
  have hp := weakGradient_locality (hf.add hfin hv) (hg.add hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  have hn := weakGradient_locality (hf.sub hfin hv) (hg.sub hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  filter_upwards [hp,hn] with x hx hy h
  simp only [gamma,hx h,hy h]

lemma gamma_zero_off_set (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f v : X → ℝ}
    (hf : LocalSobolev m f) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∉ Q → f x = 0) :
    ∀ᵐ x ∂m, x ∉ Q → gamma m f v x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [gamma_locality_left hfin hf hz hv hQ.compl he,
    abs_gamma_le hfin hpar hz hv,weakGradient_const (m := m) 0] with x hx hy hz h
  rw [hx h]
  apply abs_nonpos_iff.mp
  simpa only [hz,zero_mul] using hy
end WeakHessian

end
end InlinedFile17

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_PotentialPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile19
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [ProperSpace X] in
lemma norm_gradient_le_supported_lipschitz (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hfS : Sobolev m f) {L : ℝ≥0} (hf : LipschitzWith L f)
    {Q : Set X} (hQ : MeasurableSet Q) (hs : tsupport f ⊆ Q)
    (hD : MemLp (Q.indicator (fun _ : X => (L:ℝ))) 2 m) :
    ‖hfS.2.2.toLp (weakGradient m f)‖ ≤ ‖hD.toLp (Q.indicator (fun _ : X => (L:ℝ)))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hfS.2.2.coeFn_toLp,hD.coeFn_toLp,weakGradient_zero_off_support hfS.2.1,
    weakGradient_le_lipschitz hfin hf,weakGradient_nonneg (m := m) f,
    (ae_restrict_iff' hQ).mp (indicator_ae_eq_restrict (μ := m) (f := fun _ : X => (L:ℝ)) hQ)]
      with x he hd hz hl hn hi
  rw [he,hd,Real.norm_eq_abs,abs_of_nonneg hn]
  by_cases hx : x ∈ Q
  · simpa only [hi hx,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg] using hl
  · rw [hz (fun h => hx (hs h)),indicator_of_notMem hx,norm_zero]

omit [ProperSpace X] in
lemma integral_gamma_localization (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ x ∈ Q, f x = g x)
    (hs : ∀ᵐ x ∂m, x ∉ Q → v x = 0) :
    (∫ x,gamma m f v x ∂m) = ∫ x,gamma m g v x ∂m := by
  apply integral_congr_ae
  filter_upwards [gamma_locality_left hfin hf hg hv hQ (ae_of_all _ he),
    gamma_zero_off_set hfin hpar hv hf hQ hs,gamma_zero_off_set hfin hpar hv hg hQ hs,
    gamma_comm (m := m) f v,gamma_comm (m := m) g v] with x hl hz hy hc hd
  by_cases hx : x ∈ Q
  · exact hl hx
  · rw [hc,hd,hz hx,hy hx]

lemma CurvatureDimension.potential_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {φs : ℕ → X → ℝ} {φ g : X → ℝ} {L : ℝ≥0}
    (hφs : ∀ n, LipschitzWith L (φs n)) (hφ : LipschitzWith L φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hg : Sobolev m g) (hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → g x = 0) :
    Tendsto (fun n => ∫ x,gamma m (φs n) g x ∂m) atTop (𝓝 (∫ x,gamma m φ g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := Metric.closedBall o ((R:ℝ)+2)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  obtain ⟨k,hk⟩ := exists_nat_ge (B+(L:ℝ)*(R:ℝ))
  have hk0 : (0:ℝ) ≤ k := (add_nonneg hB (mul_nonneg L.coe_nonneg R.coe_nonneg)).trans hk
  let χ := rootCutoff o R
  let loc (v : X → ℝ) (x : X) := realClip k (v x)*χ x
  let T : ℝ≥0 := L*‖(1:ℝ)‖₊+‖(k:ℝ)‖₊*1
  have hχB (x : X) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (rootCutoff_nonneg o R x)]
    exact rootCutoff_le_one o R x
  have hlip (v : X → ℝ) (hv : LipschitzWith L v) : LipschitzWith T (loc v) := by
    have hcl : LipschitzWith L (fun x => realClip k (v x)) := by
      simpa only [one_mul,Function.comp_def] using (realClip_lipschitz k).comp hv
    exact lipschitz_mul_bounded hcl (rootCutoff_lipschitz o R) (fun x => realClip_abs_le k (v x)) hχB
  have hs (v : X → ℝ) : tsupport (loc v) ⊆ Q :=
    tsupport_mul_subset_right.trans (rootCutoff_support o R)
  have hc (v : X → ℝ) : HasCompactSupport (loc v) :=
    isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (hs v)
  have hS (v : X → ℝ) (hv : LipschitzWith L v) : Sobolev m (loc v) :=
    sobolev_of_lipschitz_compactSupport hfin (hlip v hv) (hc v)
  have he (v : X → ℝ) (hv : LipschitzWith L v) (hbv : |v o| ≤ B)
      (x : X) (hx : x ∈ Metric.closedBall o R) : loc v x = v x := by
    have hdist : dist x o ≤ R := hx
    have H : |v x| ≤ (k:ℝ) := by
      have ha : |v x| ≤ |v o|+|v x-v o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (v o) (v x)
      have hbnd := hv.dist_le_mul x o
      rw [Real.dist_eq] at hbnd
      exact (ha.trans (add_le_add hbv (hbnd.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)))).trans hk
    simp only [loc,χ,rootCutoff_one hx,mul_one,realClip,
      min_eq_left (abs_le.mp H).2,max_eq_right (abs_le.mp H).1]
  let d := Q.indicator (fun _ : X => (k:ℝ))
  have hd : MemLp d 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hdom (v : X → ℝ) : ∀ᵐ x ∂m, ‖loc v x‖ ≤ ‖d x‖ := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Q
    · simp only [loc,d,indicator_of_mem hx,norm_mul,Real.norm_eq_abs,abs_of_nonneg hk0]
      exact (mul_le_mul (realClip_abs_le k (v x)) (hχB x) (abs_nonneg _) hk0).trans_eq (mul_one _)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs v h)),norm_zero]
      exact norm_nonneg _
  have hLT : Tendsto (fun n => (hS (φs n) (hφs n)).1.toLp (loc (φs n))) atTop
      (𝓝 ((hS φ hφ).1.toLp (loc φ))) := by
    apply toLp_tendsto_of_domination (fun n => (hS (φs n) (hφs n)).1) (hS φ hφ).1 hd
      (fun n => hdom (φs n))
    exact ae_of_all _ fun x => ((realClip_lipschitz k).continuous.tendsto (φ x) |>.comp (hT x)).mul_const (χ x)
  let D := Q.indicator (fun _ : X => (T:ℝ))
  have hD : MemLp D 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hbD (n : ℕ) : ‖(hS (φs n) (hφs n)).2.2.toLp (weakGradient m (loc (φs n)))‖ ≤ ‖hD.toLp D‖ :=
    norm_gradient_le_supported_lipschitz hfin (hS (φs n) (hφs n)) (hlip _ (hφs n))
      measurableSet_closedBall (hs _) hD
  have H := hcd.integral_gamma_tendsto hfin hq o (fun n => hS _ (hφs n)) (hS φ hφ) hg hLT (norm_nonneg _) hbD
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hp (v : X → ℝ) (hv : LipschitzWith L v) (hbv : |v o| ≤ B) :
      (∫ x,gamma m (loc v) g x ∂m) = ∫ x,gamma m v g x ∂m :=
    integral_gamma_localization hfin hpar (hS v hv).2.1 (localSobolev_of_lipschitz hfin hv) hg.2.1
      measurableSet_closedBall (he v hv hbv) hgs
  simpa only [hp φ hφ hbφ,hp _ (hφs _) (hb _)] using H
end WeakHessian

end
end InlinedFile19

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyPairingLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile20
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma entropy_pairing_twice (_ : FiniteOnBoundedSets m) {u φ : X → ℝ}
    (_ : LocalSobolev m u) (_ : LocalSobolev m φ) :
    (∫ x,2*u x*gamma m φ u x ∂m) = 2*(∫ x,u x*gamma m u φ x ∂m) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gamma_comm (m := m) φ u] with x hx
  rw [hx]; ring

lemma CurvatureDimension.entropy_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {vs : ℕ → X → ℝ} {w : X → ℝ} (hvs : ∀ n, Sobolev m (vs n)) (hw : Sobolev m w)
    {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0)
    (hV : Tendsto (fun n => (hvs n).1.toLp (vs n)) atTop (𝓝 (hw.1.toLp w)))
    (hE : Tendsto (fun n => ‖((hvs n).sub hfin hw).2.2.toLp
      (weakGradient m (fun x => vs n x-w x))‖) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, ‖(hvs n).2.2.toLp (weakGradient m (vs n))‖ ≤ M)
    {φs : ℕ → X → ℝ} {φ : X → ℝ} {L : ℝ≥0}
    (hφs : ∀ n, LipschitzWith L (φs n)) (hφ : LipschitzWith L φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    Tendsto (fun n => ∫ x,2*vs n x*gamma m (φs n) (vs n) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m φ w x ∂m)) := by
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hnorm : Tendsto (fun n => ‖((hvs n).1.sub hw.1).toLp (fun x => vs n x-w x)‖)
      atTop (𝓝 0) := by
    have he (n : ℕ) : ((hvs n).1.sub hw.1).toLp (fun x => vs n x-w x) =
        (hvs n).1.toLp (vs n)-hw.1.toLp w := MemLp.toLp_sub (hvs n).1 hw.1
    simp_rw [he]
    simpa only [sub_self,norm_zero] using (hV.sub_const (hw.1.toLp w)).norm
  have hboundT := ((hnorm.const_mul (L:ℝ)).mul_const M).add
    (hE.const_mul ((L:ℝ)*‖hw.1.toLp w‖))
  simp only [mul_zero,zero_mul,zero_add] at hboundT
  have hdiff : Tendsto (fun n => (∫ x,vs n x*gamma m (vs n) (φs n) x ∂m)-
      (∫ x,w x*gamma m w (φs n) x ∂m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hboundT
    intro n
    rw [Real.norm_eq_abs]
    exact (weighted_gamma_root_difference_bound hfin hpar (hvs n) hw (hφs n)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hM n)
        (mul_nonneg L.coe_nonneg (norm_nonneg _))) le_rfl)
  have hg := hw.square_bounded hfin hA
  have hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x^2 = 0 :=
    hws.mono fun x hx h => by rw [hx h]; norm_num
  have hfixed := hcd.potential_pairing_tendsto hfin hq o R hφs hφ hB hb hbφ hT hg hgs
  have he (v : X → ℝ) (hv : LipschitzWith L v) :
      (∫ x,gamma m v (fun x => w x^2) x ∂m) = 2*(∫ x,w x*gamma m w v x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [gamma_comm (m := m) v (fun x => w x^2),
      gamma_square_bounded hfin hpar hw (localSobolev_of_lipschitz hfin hv) hA] with x hc hs
    rw [hc,hs]; ring
  have H := (hdiff.const_mul 2).add hfixed
  simp only [mul_zero,zero_add,he _ (hφs _),he φ hφ] at H
  simp_rw [entropy_pairing_twice hfin (hvs _).2.1 (localSobolev_of_lipschitz hfin (hφs _)),
    entropy_pairing_twice hfin hw.2.1 (localSobolev_of_lipschitz hfin hφ)]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  ring
end WeakHessian

end
end InlinedFile20

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CostConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile10
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X] {m : Measure X}

lemma bounded_plan_potentials {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (o : X) (R : ℝ≥0) (hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    {π : Measure (Curve X)} (ho : IsOptimalCoupling (endpointCoupling π) μ ν) :
    ∃ φ ψ : X → ℝ, LipschitzWith (2*R) φ ∧ LipschitzWith (2*R) ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 := by
  obtain ⟨φ,ψ,hφ,hψ,hd,hc⟩ := WeakHessianTransport.bounded_support_kantorovich_potentials
    (isCompact_closedBall o R) (Metric.nonempty_closedBall.mpr R.coe_nonneg) μ ν hμ hν ho
    (R := 2*R) (by
      intro x hx y hy
      have H := dist_triangle x o y
      rw [dist_comm o y] at H
      change dist x o ≤ R at hx
      change dist y o ≤ R at hy
      push_cast
      linarith)
  refine ⟨φ,ψ,hφ,hψ,hd,?_⟩
  apply (ae_map_iff ((continuous_eval_const timeZero).prodMk (continuous_eval_const timeOne)).measurable.aemeasurable ?_).mp hc
  exact (isClosed_eq ((hφ.continuous.comp continuous_fst).add (hψ.continuous.comp continuous_snd))
    (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet

lemma optimal_energy_squareDensity_bound {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    [IsProbabilityMeasure (squareDensityMeasure m f)] [IsProbabilityMeasure (squareDensityMeasure m g)]
    {ν : Measure X} [IsProbabilityMeasure ν] (o : X) (R : ℝ≥0)
    (hsf : ∀ᵐ x ∂squareDensityMeasure m f, x ∈ Metric.closedBall o R)
    (hsg : ∀ᵐ x ∂squareDensityMeasure m g, x ∈ Metric.closedBall o R)
    (hsν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hbπ : BoundedTracks π) (hbη : BoundedTracks η)
    (hoπ : IsOptimalCoupling (endpointCoupling π) (squareDensityMeasure m f) ν)
    (hoη : IsOptimalCoupling (endpointCoupling η) (squareDensityMeasure m g) ν) :
    |planEnergy π-planEnergy η| ≤ 4*(R:ℝ)^2*(∫ x,|f x^2-g x^2| ∂m) := by
  have aux {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
      (hu2 : MemLp u 2 m) (hv2 : MemLp v 2 m)
      [IsProbabilityMeasure (squareDensityMeasure m u)] [IsProbabilityMeasure (squareDensityMeasure m v)]
      (hsu : ∀ᵐ x ∂squareDensityMeasure m u, x ∈ Metric.closedBall o R)
      (hsv : ∀ᵐ x ∂squareDensityMeasure m v, x ∈ Metric.closedBall o R)
      {p q : Measure (Curve X)} [IsProbabilityMeasure p] [IsProbabilityMeasure q]
      (hbp : BoundedTracks p) (hbq : BoundedTracks q)
      (hop : IsOptimalCoupling (endpointCoupling p) (squareDensityMeasure m u) ν)
      (hoq : IsOptimalCoupling (endpointCoupling q) (squareDensityMeasure m v) ν) :
      planEnergy p-planEnergy q ≤ 4*(R:ℝ)^2*(∫ x,|u x^2-v x^2| ∂m) := by
    obtain ⟨φ,ψ,hφ,hψ,hd,hc⟩ := bounded_plan_potentials o R hsu hsν hop
    obtain ⟨hp0,hp1⟩ := hop.1.interpolation_endpoints
    obtain ⟨hq0,hq1⟩ := hoq.1.interpolation_endpoints
    have H := planEnergy_le_of_contact hbp hbq hbp.integrable_length_sq hbq.integrable_length_sq
      hφ hψ hd hc (hp1.trans hq1.symm)
    rw [hp0,hq0] at H
    have J := squareDensity_pairing_bound_supported hu hv hu2 hv2 hφ o R hsu hsv
    push_cast at J
    nlinarith [le_abs_self ((∫ x,φ x ∂squareDensityMeasure m u)-(∫ x,φ x ∂squareDensityMeasure m v))]
  apply abs_le.mpr
  constructor
  · have H := aux hg hf hg2 hf2 hsg hsf hbη hbπ hoη hoπ
    simp only [abs_sub_comm (g _^2)] at H
    linarith
  · exact aux hf hg hf2 hg2 hsf hsg hbπ hbη hoπ hoη

lemma optimal_energy_squareDensity_tendsto {fs : ℕ → X → ℝ} {w : X → ℝ}
    (hfm : ∀ n, Measurable (fs n)) (hwm : Measurable w)
    (hfs : ∀ n, MemLp (fs n) 2 m) (hw : MemLp w 2 m)
    (hP : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fs n)))
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.toLp w)))
    {ν : Measure X} [IsProbabilityMeasure ν] (o : X) (R : ℝ≥0)
    (hsf : ∀ n, ∀ᵐ x ∂squareDensityMeasure m (fs n), x ∈ Metric.closedBall o R)
    (hsw : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R)
    (hsν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    (ps : ℕ → ProbabilityMeasure (Curve X)) (η : ProbabilityMeasure (Curve X))
    (hbps : ∀ n, BoundedTracks (ps n:Measure (Curve X))) (hbη : BoundedTracks (η:Measure (Curve X)))
    (hops : ∀ n, IsOptimalCoupling (endpointCoupling (ps n:Measure (Curve X))) (squareDensityMeasure m (fs n)) ν)
    (hoη : IsOptimalCoupling (endpointCoupling (η:Measure (Curve X))) (squareDensityMeasure m w) ν) :
    Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (planEnergy (η:Measure (Curve X)))) := by
  have H := (squareDensity_L1_tendsto hfs hw hF).const_mul (4*(R:ℝ)^2)
  simp only [mul_zero] at H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ H
  intro n
  let := hP n
  exact optimal_energy_squareDensity_bound (hfm n) hwm (hfs n) hw o R (hsf n) hsw hsν
    (hbps n) hbη (hops n) hoη
end WeakHessian

end
end InlinedFile10

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_SobolevFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile12
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma sqrt_gradient_energy_le_upper {v D : X → ℝ} (hv : Sobolev m v)
    (hD : IsLocalWeakUpperGradient m v D) (hD2 : MemLp D 2 m) :
    Real.sqrt (∫ x,(weakGradient m v x)^2 ∂m) ≤ ‖hD2.toLp D‖ := by
  have H : (∫ x,(weakGradient m v x)^2 ∂m) ≤ ∫ x,D x^2 ∂m := by
    apply integral_mono_ae ((memLp_two_iff_integrable_sq hv.2.2.aestronglyMeasurable).mp hv.2.2)
      ((memLp_two_iff_integrable_sq hD2.aestronglyMeasurable).mp hD2)
    filter_upwards [(weakGradient_isMinimal hv.2.1.2).2 D hD,weakGradient_nonneg (m := m) v] with x hx hn
    nlinarith
  rw [← norm_toLp_sq_eq_integral hD2] at H
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt H

end WeakHessian

end
end InlinedFile12

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_StrongRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile14
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.energy_tendsto_of_upper_bound
    {ι : Type*} {l : Filter ι} (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    (bs : ι → ℝ) (hb : ∀ i, hQ.realEnergy (us i) ≤ bs i)
    (hbs : Tendsto bs l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u)) := by
  have he (v : hQ.domain) : ENNReal.ofReal (hQ.realEnergy v) = Q v :=
    ENNReal.ofReal_toReal v.property.ne
  have hbs' : Tendsto (fun i => ENNReal.ofReal (bs i)) l (𝓝 (Q u)) := by
    rw [← he u]
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp hbs
  have hQlim : Tendsto (fun i => Q (us i)) l (𝓝 (Q u)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hu (hQ.lowerSemicontinuous u a ha)
    · intro b hb'
      filter_upwards [hbs'.eventually_lt_const hb'] with i hi
      rw [← he (us i)]
      exact (ENNReal.ofReal_le_ofReal (hb i)).trans_lt hi
  exact ENNReal.continuousAt_toReal u.property.ne |>.tendsto.comp hQlim
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.strong_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {w : X → ℝ} (hw : Sobolev m w)
    (fs Ds : ℕ → X → ℝ) (hfs : ∀ n, MemLp (fs n) 2 m) (hDs : ∀ n, MemLp (Ds n) 2 m)
    (hUG : ∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n))
    (hfT : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)))
    (hDT : Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w)))) :
    ∃ hs : ∀ n, Sobolev m (fun x => fs n x-w x),
      Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖)
        atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let hS (n : ℕ) := Sobolev.of_upperGradient hfin (hfs n) (hUG n) (hDs n)
  let Q := cheeger_closedQuadraticEnergy hq
  let u : Q.domain := ⟨hw.1.toLp w,by
    change cheegerEnergy m (hw.1.toLp w : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hw.1).mp hw⟩
  let us (n : ℕ) : Q.domain := ⟨(hfs n).toLp (fs n),by
    change cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o (hfs n)).mp (hS n)⟩
  have eu : Q.realEnergy u = ‖hw.2.2.toLp (weakGradient m w)‖^2/2 := by
    change (cheegerEnergy m (hw.1.toLp w : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hw,
      norm_toLp_sq_eq_integral hw.2.2]
  let bs (n : ℕ) := ‖(hDs n).toLp (Ds n)‖^2/2
  have hbs : Tendsto bs atTop (𝓝 (Q.realEnergy u)) := by
    rw [eu]
    exact hDT.norm.pow 2 |>.div_const 2
  have hb (n : ℕ) : Q.realEnergy (us n) ≤ bs n := by
    change (cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ)).toReal ≤ _
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hS n)]
    dsimp [bs]
    rw [norm_toLp_sq_eq_integral (hDs n)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply integral_mono_ae (hS n).2.2.integrable_sq (hDs n).integrable_sq
    filter_upwards [(weakGradient_isMinimal (hS n).2.1.2).2 _ (hUG n),
      weakGradient_nonneg (m := m) (fs n)] with x hx hn
    nlinarith
  obtain ⟨M,hM,hMb⟩ := (Metric.isBounded_range_of_tendsto bs hbs).exists_pos_norm_le
  have hbM (n : ℕ) : Q.realEnergy (us n) ≤ M :=
    (hb n).trans ((le_abs_self _).trans (hMb _ (mem_range_self n)))
  have hE := Q.energy_tendsto_of_upper_bound us u hfT bs hb hbs
  have hsub := Q.form_energy_sub_tendsto (cheeger_domain_dense hq) us u hfT hM.le hbM hE
  let hs (n : ℕ) := (hS n).sub hfin hw
  refine ⟨hs,?_⟩
  have he (n : ℕ) : ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2 =
      2*Q.realEnergy (us n-u) := by
    rw [norm_toLp_sq_eq_integral (hs n).2.2]
    have hae : ((us n-u : Q.domain):Lp ℝ 2 m) = (hs n).1.toLp (fun x => fs n x-w x) := by
      exact (MemLp.toLp_sub (hfs n) hw.1).symm
    change _ = 2*(cheegerEnergy m (((us n-u : Q.domain):Lp ℝ 2 m) : X → ℝ)).toReal
    rw [hae,cheegerEnergy_congr_ae (hs n).1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hs n)]
    ring
  have H : Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2)
      atTop (𝓝 0) := by simpa only [he,mul_zero] using hsub.const_mul 2
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using H.sqrt
end WeakHessian

end
end InlinedFile14

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevSubdifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile22
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.compact_sobolev_entropy_subdifferential_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      LipschitzWith (2*(R+2)) φ ∧ LipschitzWith (2*(R+2)) ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  have hsw : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R := by rw [← hμ]; exact ae_iff.mpr hsμ
  obtain ⟨vs,hLip,hvb,hvsupp,hvs,hvp,Ds,hDs,hUG,hV,hD⟩ :=
    hrcd.1.normalized_compact_root_approximation hfin hw hwm hB hwn hwB o R (squareDensity_zero_outside hwm hsw)
  let Q : ℝ≥0 := R+2
  let D : ℝ≥0∞ := C+ENNReal.ofReal ((2*B)^2)+1
  have hDt : D ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hCt,ENNReal.ofReal_ne_top⟩,ENNReal.one_ne_top⟩
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hCD : C ≤ D := le_trans le_self_add le_self_add
  have hBD : ENNReal.ofReal ((2*B)^2) ≤ D := le_trans le_add_self le_self_add
  have hBsmall : ENNReal.ofReal (B^2) ≤ D :=
    (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg B])).trans hBD
  have hdμ : (μ:Measure X) ≤ D • m := by
    rw [hμ]; exact dominated_mono_constant (squareDensity_le_of_bound hB hwn hwB) hBsmall
  have hdνD := dominated_mono_constant hdν hCD
  have hsμQ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  have hsνQ : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  let μs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (vs n) (hvp n)
  have hms (n : ℕ) : (μs n:Measure X) = squareDensityMeasure m (vs n) := rfl
  have hds (n : ℕ) : (μs n:Measure X) ≤ D • m := by
    exact dominated_mono_constant (squareDensity_le_of_bound (by positivity : 0 ≤ 2*B)
      (ae_of_all _ fun x => (hvb n x).1) (ae_of_all _ fun x => (hvb n x).2)) hBD
  have hss (n : ℕ) : ∀ᵐ x ∂(μs n:Measure X), x ∈ Metric.closedBall o Q := by
    apply squareDensity_ae_support (vs n).continuous.measurable
    apply ae_of_all
    intro x hx
    have H : x ∉ tsupport (vs n) := fun h => hx (by simpa only [Q,NNReal.coe_add,NNReal.coe_ofNat] using hvsupp n h)
    exact image_eq_zero_of_notMem_tsupport H
  obtain ⟨π,hπ,hb,hgeo,hopt,hE,hchord,hcomp⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ ν o Q (ae_iff.mp hsμQ) (ae_iff.mp hsνQ) hD0 hDt hdμ hdνD
  have hex (n : ℕ) := hrcd.bounded_entropy_subdifferential hN hfin (vs n) (hLip n).choose_spec
    (fun x => (hvb n x).1) (μs n) ν (hms n) o Q (ae_iff.mp (hss n)) (ae_iff.mp hsνQ) hD0 hDt (hds n) hdνD
  choose ps φ ψ hps hbps hgps hops hφ hψ hdual hcontact hent using hex
  let fs (n : ℕ) (x : X) := φ n x-φ n o
  let gs (n : ℕ) (x : X) := ψ n x+φ n o
  have hf (n : ℕ) : LipschitzWith (2*Q) (fs n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [fs,Real.dist_eq,sub_sub_sub_cancel_right] using (hφ n).dist_le_mul x y
  have hg (n : ℕ) : LipschitzWith (2*Q) (gs n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [gs,Real.dist_eq,add_sub_add_right_eq_sub] using (hψ n).dist_le_mul x y
  have hfd (n : ℕ) (x y : X) : fs n x+gs n y ≤ dist x y^2/2 := by
    dsimp [fs,gs]; linarith [hdual n x y]
  have hfc (n : ℕ) : ∀ᵐ γ ∂(ps n:Measure (Curve X)), fs n (γ timeZero)+gs n (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := (hcontact n).mono fun γ hc => by dsimp [fs,gs]; linarith
  have hgb (n : ℕ) : |gs n o| ≤ 2*(2*Q:ℝ≥0)*Q := by
    apply centered_dual_bound (hf n) (hg n) o Q (sub_self _) (hfd n) (hfc n)
    have H0 : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeZero ∈ Metric.closedBall o Q := by
      apply (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable measurableSet_closedBall).mp
      change ∀ᵐ x ∂interpolation (ps n:Measure (Curve X)) timeZero, x ∈ Metric.closedBall o Q
      rw [(hops n).1.interpolation_endpoints.1]
      exact hss n
    have H1 : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ Metric.closedBall o Q := by
      apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable measurableSet_closedBall).mp
      change ∀ᵐ x ∂interpolation (ps n:Measure (Curve X)) timeOne, x ∈ Metric.closedBall o Q
      rw [(hops n).1.interpolation_endpoints.2]
      exact hsνQ
    exact H0.and H1
  obtain ⟨f,g,s,hs,hfL,hgL,hfo,hgo,hfT,hgT,hfg⟩ := exists_dual_subsequence o fs gs hf hg
    (by positivity : 0 ≤ 2*(2*Q:ℝ≥0)*Q) (fun n => by dsimp [fs]; simp only [sub_self,abs_zero]; positivity)
    hgb hfd
  have hcost : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (planEnergy (π:Measure (Curve X)))) := by
    apply optimal_energy_squareDensity_tendsto (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp hV o Q hss
      (by rw [← hμ]; exact hsμQ) hsνQ ps π hbps hb (fun n => hops n)
    simpa only [← hμ] using hopt
  have hsμs : Tendsto μs atTop (𝓝 μ) := by
    have H := squareDensity_tendsto_probability (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp inferInstance hV
    have he : squareDensityProbability m w inferInstance = μ := by apply Subtype.ext; exact hμ.symm
    rwa [he] at H
  have hIf : Tendsto (fun n => ∫ x,fs (s n) x ∂(μs (s n):Measure X)) atTop (𝓝 (∫ x,f x ∂(μ:Measure X))) := by
    rw [hμ]
    exact squareDensity_varying_pairing_tendsto (fun n => (vs (s n)).continuous.measurable) hwm
      (fun n => hvs (s n)) hw.1 (fun n => hvp (s n)) (hV.comp hs.tendsto_atTop) o Q
      (fun n => hss (s n)) (by rw [← hμ]; exact hsμQ) (fun n => hf (s n))
      (B := 0) (fun n => by simp [fs]) hfT
  have hIg := lipschitz_integral_tendsto_supported o Q hsνQ (fun n => hg (s n))
    (fun n => hgb (s n)) hgT
  have hc : ∀ᵐ γ ∂(π:Measure (Curve X)), f (γ timeZero)+g (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := by
    apply contact_of_integral_eq hb hb.integrable_length_sq hfL hgL hfg
    rw [hopt.1.interpolation_endpoints.1,hopt.1.interpolation_endpoints.2]
    apply tendsto_nhds_unique (hIf.add hIg)
    have he (n : ℕ) : (∫ x,fs (s n) x ∂(μs (s n):Measure X))+
        (∫ x,gs (s n) x ∂(ν:Measure X)) = planEnergy (ps (s n):Measure (Curve X))/2 := by
      have H := contact_integral_eq (hbps (s n)) (hf (s n)) (hg (s n)) (hfc (s n))
      rwa [(hops (s n)).1.interpolation_endpoints.1,(hops (s n)).1.interpolation_endpoints.2] at H
    simp_rw [he]
    exact hcost.comp hs.tendsto_atTop |>.div_const 2
  have hS (n : ℕ) : Sobolev m (vs n) := Sobolev.of_upperGradient hfin (hvs n) (hUG n) (hDs n)
  obtain ⟨hsub,hsubT⟩ := hrcd.1.strong_root_approximation hfin hrcd.2 o hw
    (fun n => (vs n:X → ℝ)) Ds hvs hDs hUG hV hD
  obtain ⟨M,hM,hMb⟩ := (Metric.isBounded_range_of_tendsto (fun n => ‖(hDs n).toLp (Ds n)‖) hD.norm).exists_pos_norm_le
  have hgrad (n : ℕ) : ‖(hS n).2.2.toLp (weakGradient m (vs n))‖ ≤ M := by
    have H := sqrt_gradient_energy_le_upper (hS n) (hUG n) (hDs n)
    rw [← norm_toLp_sq_eq_integral (hS n).2.2,Real.sqrt_sq (norm_nonneg _)] at H
    exact H.trans (by simpa only [Real.norm_eq_abs,abs_norm] using hMb _ (mem_range_self n))
  have hpair : Tendsto (fun n => ∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m f w x ∂m)) := by
    apply hrcd.1.entropy_pairing_tendsto hfin hrcd.2 o R (fun n => hS (s n)) hw
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2)
      (squareDensity_zero_outside hwm hsw) (hV.comp hs.tendsto_atTop)
      (hsubT.comp hs.tendsto_atTop) (fun n => hgrad (s n)) (fun n => hf (s n)) hfL
      (by positivity : 0 ≤ 2*(2*Q:ℝ≥0)*Q) (fun n => by simp only [fs,sub_self,abs_zero]; exact NNReal.coe_nonneg _) hfo hfT
  have hent' (n : ℕ) : entropyReal m (μs (s n):Measure X) ≤ entropyReal m (ν:Measure X)+
      (∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m)-K/2*planEnergy (ps (s n):Measure (Curve X)) := by
    have he : (∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m) =
        ∫ x,2*vs (s n) x*gamma m (φ (s n)) (vs (s n)) x ∂m := by
      apply integral_congr_ae
      have H := gamma_add_const_left hfin (localSobolev_of_lipschitz hfin (hφ (s n))) (hS (s n)).2.1 (-φ (s n) o)
      filter_upwards [H] with x hx
      simp only [fs,sub_eq_add_neg,hx]
    rw [he]
    linarith [hent (s n)]
  have hlim := (tendsto_const_nhds (x := entropyReal m (ν:Measure X))).add hpair |>.sub
    ((hcost.comp hs.tendsto_atTop).const_mul (K/2))
  have H := entropyReal_le_of_tendsto_supported hfin (fun n => μs (s n)) μ
    (hsμs.comp hs.tendsto_atTop) o Q (fun n => hss (s n)) hsμQ hDt (fun n => hds (s n)) hdμ hlim hent'
  exact ⟨π,f,g,hπ,hb,hgeo,hopt,hfL,hgL,hfg,hc,by linarith⟩
end WeakHessian

end
end InlinedFile22

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential_oai.{u_1} := @OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential_oai.{u_1}
