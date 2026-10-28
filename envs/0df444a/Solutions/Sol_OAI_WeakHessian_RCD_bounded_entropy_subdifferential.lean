-- Prove2me | solution 1 for OAI.WeakHessian.RCD.bounded_entropy_subdifferential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:54:34.430995+00:00
-- url     : https://prove2.me/submissions/3271ec32-7fc7-4795-8c7f-e1a2337a7dfd

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_IntegralEvalDifference
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
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [m.WeaklyRegular]

omit [m.WeaklyRegular] in
lemma integral_eval_difference_le {π : Measure (Curve X)} {C : ℝ≥0}
    (hC : ∀ t : Time, π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m)
    {f g : X → ℝ} (hf : Integrable f m) (hg : Integrable g m) (t : Time) :
    |(∫ γ, f (γ t) ∂π)-(∫ γ, g (γ t) ∂π)| ≤ C * ∫ x, |f x-g x| ∂m := by
  have hm : Measurable (fun γ : Curve X => γ t) := (continuous_eval_const t).measurable
  have hf' := ((hf.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable hm.aemeasurable
  have hg' := ((hg.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable hm.aemeasurable
  dsimp only [Function.comp_def] at hf' hg'
  rw [← integral_sub hf' hg']
  calc
    |∫ γ, f (γ t)-g (γ t) ∂π| ≤ ∫ γ, |f (γ t)-g (γ t)| ∂π := abs_integral_le_integral_abs
    _ = ∫ x, |f x-g x| ∂(π.map (fun γ => γ t)) :=
      (integral_map hm.aemeasurable (((hf.sub hg).abs.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).1).symm
    _ ≤ ∫ x, |f x-g x| ∂((C:ℝ≥0∞) • m) :=
      integral_mono_measure (hC t) (ae_of_all _ fun x => abs_nonneg _) ((hf.sub hg).abs.smul_measure ENNReal.coe_ne_top)
    _ = _ := by rw [integral_smul_measure]; rfl

lemma IsTestPlan.continuous_integral_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : Integrable f m) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨C,hC⟩ := hπ.2.1
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε/(3*((C:ℝ)+1)) := by positivity
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hb (t : Time) : |(∫ γ, f (γ t) ∂π)-(∫ γ, g (γ t) ∂π)| ≤ ε/3 := by
    have H := integral_eval_difference_le hC hf hgi t
    have hh : (∫ x, |f x-g x| ∂m) ≤ ε/(3*((C:ℝ)+1)) := by simpa only [Real.norm_eq_abs] using hg
    have hc : (C:ℝ)/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ ≤ C * (ε/(3*((C:ℝ)+1))) := H.trans (mul_le_mul_of_nonneg_left hh C.coe_nonneg)
      _ = ε/3 * ((C:ℝ)/(C+1)) := by field_simp
      _ ≤ ε/3 := by nlinarith
  have hgc : Continuous (fun t : Time => ∫ γ, g (γ t) ∂π) := by
    apply continuous_of_dominated (bound := fun _ => ‖g‖)
    · intro t
      exact (g.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
    · intro t
      exact ae_of_all _ fun γ => g.norm_coe_le_norm (γ t)
    · exact integrable_const _
    · exact ae_of_all _ fun γ => g.continuous.comp γ.continuous
  have hev := (Metric.tendsto_nhds.mp (hgc.continuousAt (x := s))) (ε/3) (by positivity)
  filter_upwards [hev] with t ht
  rw [Real.dist_eq] at ht ⊢
  have H := abs_sub_le (∫ γ, f (γ t) ∂π) (∫ γ, g (γ t) ∂π) (∫ γ, g (γ s) ∂π)
  have J := abs_sub_le (∫ γ, f (γ t) ∂π) (∫ γ, g (γ s) ∂π) (∫ γ, f (γ s) ∂π)
  have hh := hb s
  rw [abs_sub_comm] at hh
  linarith [hb t]

end WeakHessian

end
end InlinedFile0

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
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_FiniteLocalization
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
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.finite_localization (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∃ S : Set X, MeasurableSet S ∧ IsFiniteMeasure (m.restrict S) ∧
      IsTestPlan (m.restrict S) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  let S := Metric.closedBall o R
  have hS : MeasurableSet S := measurableSet_closedBall
  have hfin : IsFiniteMeasure (m.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfinite _ Metric.isBounded_closedBall⟩
  refine ⟨S,hS,hfin,hπ.1,?_,hπ.2.2⟩
  obtain ⟨C,hC⟩ := hπ.2.1
  refine ⟨C,fun t => ?_⟩
  have ha : ∀ᵐ x ∂(π.map (fun γ => γ t)), x ∈ S := by
    apply ae_map_iff (continuous_eval_const t).measurable.aemeasurable hS |>.mpr
    exact hb.mono fun γ hγ => hγ t
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  convert Measure.restrict_mono le_rfl (hC t) using 1
  all_goals try with_reducible_and_instances rfl
  exact (Measure.restrict_smul _ _ _).symm

lemma IsTestPlan.continuous_integral_eval_bounded (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} (hf : AEMeasurable f m) {B : ℝ} (hB : ∀ᵐ x ∂m, |f x| ≤ B) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  obtain ⟨S,hS,hfin,hplan⟩ := hπ.finite_localization hfinite hb
  let : IsFiniteMeasure (m.restrict S) := hfin
  apply hplan.continuous_integral_eval
  exact (integrable_const B).mono' hf.restrict.aestronglyMeasurable
    (ae_restrict_of_ae (hB.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx))

end WeakHessian

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
lemma IsGeodesic.ae_metricSpeed_le {γ : Curve X} (h : IsGeodesic γ) :
    ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),
      metricSpeed γ s ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
  h.squareControl.metricSpeed_le

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

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {B : ℝ} (hB : 0 ≤ B) (hDb : ∀ᵐ x ∂m, |D x| ≤ B)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫ z : Curve X × ℝ, ((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2
        ∂(π.prod (volume.restrict (Icc (0:ℝ) t.val))) := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) := by
    apply (integrable_const (B^2)).mono' (hDm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_mono hprod (hπ.ae_prod_eval_of_ae hDb)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hz
  have hLI := hb.integrable_length_sq.comp_fst ν
  have hI := (hDI.add hLI).div_const (2:ℝ)
  dsimp only [Pi.add_apply] at hI
  have hn : 0 ≤ᵐ[π.prod ν] (fun z : Curve X × ℝ =>
      ((D (evalReal z.1 z.2))^2+dist (z.1 timeZero) (z.1 timeOne)^2)/2) :=
    ae_of_all _ fun z => by positivity
  have H : ENNReal.ofReal (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ∫⁻ z : Curve X × ℝ, ENNReal.ofReal (((D (evalReal z.1 z.2))^2+
        dist (z.1 timeZero) (z.1 timeOne)^2)/2) ∂(π.prod ν) := by
    calc
      _ ≤ ENNReal.ofReal |∫ γ, f (γ timeZero)-f (γ t) ∂π| := ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ γ, ENNReal.ofReal |f (γ timeZero)-f (γ t)| ∂π := by
        simpa only [Real.enorm_eq_ofReal_abs] using
          enorm_integral_le_lintegral_enorm (μ := π) (fun γ => f (γ timeZero)-f (γ t))
      _ ≤ ∫⁻ γ, ∫⁻ s, ENNReal.ofReal (((D (evalReal γ s))^2+
          dist (γ timeZero) (γ timeOne)^2)/2) ∂ν ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hD.ae_subinterval_le hf hπ hb timeZero t ht,hgeo,
          hπ.ae_ae_eval_of_ae hD.2.1] with γ hg hγ hpos
        rw [abs_sub_comm] at hg
        apply hg.trans
        apply lintegral_mono_ae
        filter_upwards [ae_mono hν hγ.ae_metricSpeed_le,ae_mono hν hpos] with s hs hDs
        calc
          _ ≤ ENNReal.ofReal (D (evalReal γ s))*ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
            mul_le_mul_of_nonneg_left hs bot_le
          _ = ENNReal.ofReal (D (evalReal γ s)*dist (γ timeZero) (γ timeOne)) := (ENNReal.ofReal_mul hDs).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (D (evalReal γ s)-dist (γ timeZero) (γ timeOne))])
      _ = _ := (lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hI hn] at H
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hn)).mp H


lemma IsLocalWeakUpperGradient.geodesic_young_time
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {B : ℝ} (hB : 0 ≤ B) (hDb : ∀ᵐ x ∂m, |D x| ≤ B)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) (t : Time) (ht : 0 < t.val) :
    (∫ γ, f (γ timeZero)-f (γ t) ∂π) ≤
      ((∫ s in 0..t.val, ∫ γ, (D (evalReal γ s))^2 ∂π)+
        t.val*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π))/2 := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0:ℝ) t.val)
  have hν : ν ≤ volume.restrict (Icc (0:ℝ) 1) :=
    Measure.restrict_mono_set _ (Icc_subset_Icc le_rfl t.property.2)
  have hprod : π.prod ν ≤ π.prod (volume.restrict (Icc (0:ℝ) 1)) := Measure.prod_mono le_rfl hν
  have hDm := (hπ.aemeasurable_evalReal hD.1.aemeasurable).mono_measure hprod
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) := by
    apply (integrable_const (B^2)).mono' (hDm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_mono hprod (hπ.ae_prod_eval_of_ae hDb)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hz
  have hLI := hb.integrable_length_sq.comp_fst ν
  have H := hD.geodesic_young hf hB hDb hπ hb hgeo t ht
  calc
    _ ≤ _ := H
    _ = _ := by
      rw [integral_div,integral_add hDI hLI,integral_prod_symm _ hDI,integral_prod _ hLI]
      simp only [ν,integral_const,Measure.real,Measure.restrict_apply_univ,
        Real.volume_Icc,sub_zero,smul_eq_mul,ENNReal.toReal_ofReal ht.le]
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.le]

lemma IsTestPlan.continuous_gradient_energy (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Continuous (fun s : ℝ => ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π) := by
  have hfS := localSobolev_of_lipschitz hfinite hf
  have hm := (weakGradient_isMinimal hfS.2).1.1.aemeasurable
  have hbD : ∀ᵐ x ∂m, |(weakGradient m f x)^2| ≤ (L:ℝ)^2 := by
    filter_upwards [weakGradient_le_lipschitz hfinite hf,weakGradient_nonneg (m := m) f] with x hx hn
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hn L.coe_nonneg).mpr hx
  exact (hπ.continuous_integral_eval_bounded hfinite hb (hm.pow_const 2) hbD).comp continuous_clampTime

lemma IsTestPlan.tendsto_average_gradient_energy (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun t : ℝ => (∫ s in 0..t, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)) := by
  have hc := hπ.continuous_gradient_energy hfinite hb hf
  have H := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).tendsto_slope_zero_right
  have he : clampTime 0 = timeZero := Subtype.ext (by simp [clampTime,timeZero])
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,smul_eq_mul,
    evalReal,he,div_eq_mul_inv,mul_comm] using H

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AscendingSlope
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
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma ascendingSlope_eq_iInf (f : X → ℝ) (x : X) :
    ascendingSlope f x = ⨅ n : ℕ, ascendingSlopeApprox f n x := by
  rw [ascendingSlope,nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := x)).inf_principal ({x}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy.1 le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    by_cases he : y = x
    · simp [he]
    · exact le_iSup_of_le y (le_iSup_of_le ⟨hy,he⟩ le_rfl)

lemma ascendingSlopeApprox_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (n : ℕ) (x : X) :
    ascendingSlopeApprox f n x ≤ L := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  calc
    ENNReal.ofReal ((f y-f x)/dist y x) ≤ ENNReal.ofReal (|f y-f x|/dist y x) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) dist_nonneg)
    _ ≤ slopeApprox f n x := le_iSup_of_le y (le_iSup_of_le hy le_rfl)
    _ ≤ L := slopeApprox_le_lipschitz hf n x

lemma ascendingSlope_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    ascendingSlope f x ≤ L := by
  rw [ascendingSlope_eq_iInf]
  exact (iInf_le _ 0).trans (ascendingSlopeApprox_le hf 0 x)

lemma lowerSemicontinuous_ascendingSlopeApprox {f : X → ℝ} (hf : Continuous f) (n : ℕ) :
    LowerSemicontinuous (ascendingSlopeApprox f n) := by
  intro x a ha
  obtain ⟨y,hy⟩ := lt_iSup_iff.mp ha
  obtain ⟨hy,hay⟩ := lt_iSup_iff.mp hy
  have hyx : y ≠ x := by intro he; simp [he] at hay
  have hd : ContinuousAt (fun z => dist y z) x := (continuous_const.dist continuous_id).continuousAt
  have hq : ContinuousAt (fun z => ENNReal.ofReal ((f y-f z)/dist y z)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((continuous_const.sub hf).continuousAt.div hd (dist_ne_zero.mpr hyx))
  filter_upwards [hd.eventually_lt continuousAt_const hy,
    continuousAt_const.eventually_lt hq hay] with z hz hqz
  exact hqz.trans_le (le_iSup_of_le y (le_iSup_of_le hz le_rfl))

lemma measurable_ascendingSlope [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (ascendingSlope f) := by
  simp_rw [show ascendingSlope f = fun x => ⨅ n,ascendingSlopeApprox f n x from
    funext (ascendingSlope_eq_iInf f)]
  exact Measurable.iInf fun n => (lowerSemicontinuous_ascendingSlopeApprox hf n).measurable

lemma ascending_quotient_limsup_le {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    limsup (fun s => ENNReal.ofReal ((f (evalReal γ s)-f (evalReal γ t))/|s-t|)) (𝓝[≠] t) ≤
      ascendingSlopeApprox f n (evalReal γ t)*metricSpeed γ t := by
  have hγc : Continuous (evalReal γ) := continuous_evalReal.comp (continuous_const.prodMk continuous_id)
  have hn : ∀ᶠ s in 𝓝 t, dist (evalReal γ s) (evalReal γ t) < 1/(n+1:ℝ) := by
    apply (hγc.dist continuous_const).continuousAt.eventually_lt continuousAt_const
    simp only [dist_self]
    positivity
  calc
    _ ≤ limsup (fun s => ascendingSlopeApprox f n (evalReal γ t)*ENNReal.ofReal
        (dist (evalReal γ s) (evalReal γ t)/|s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with s hs
      by_cases he : evalReal γ s = evalReal γ t
      · simp [he]
      have hdne := dist_ne_zero.mpr he
      have hid : (f (evalReal γ s)-f (evalReal γ t))/|s-t| =
          ((f (evalReal γ s)-f (evalReal γ t))/dist (evalReal γ s) (evalReal γ t))*
            (dist (evalReal γ s) (evalReal γ t)/|s-t|) := by field_simp
      rw [hid,ENNReal.ofReal_mul' (div_nonneg dist_nonneg (abs_nonneg _))]
      apply mul_le_mul_left
      exact le_iSup_of_le (evalReal γ s) (le_iSup_of_le hs le_rfl)
    _ = _ := ENNReal.limsup_const_mul_of_ne_top
       (ne_top_of_le_ne_top ENNReal.coe_ne_top (ascendingSlopeApprox_le hf n _))

lemma deriv_comp_le_ascendingSlopeApprox {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ascendingSlopeApprox f n (evalReal γ t)*metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · let u := fun s => f (evalReal γ s)
    change DifferentiableAt ℝ u t at hd
    have Hd : Tendsto (fun s => (u s-u t)/(s-t)) (𝓝[≠] t) (𝓝 (deriv u t)) := by
      simpa only [slope_fun_def_field] using
        hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have hrle : 𝓝[>] t ≤ 𝓝[≠] t := nhdsWithin_mono _ (fun s hs => ne_of_gt hs)
    have hlle : 𝓝[<] t ≤ 𝓝[≠] t := nhdsWithin_mono _ (fun s hs => ne_of_lt hs)
    have Hr : Tendsto (fun s => ENNReal.ofReal ((u s-u t)/|s-t|))
        (𝓝[>] t) (𝓝 (ENNReal.ofReal (deriv u t))) := by
      apply (ENNReal.tendsto_ofReal (Hd.mono_left hrle)).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [abs_of_pos (sub_pos.mpr hs)]
    have Hl : Tendsto (fun s => ENNReal.ofReal ((u s-u t)/|s-t|))
        (𝓝[<] t) (𝓝 (ENNReal.ofReal (-deriv u t))) := by
      apply (ENNReal.tendsto_ofReal (Hd.mono_left hlle).neg).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [abs_of_neg (sub_neg.mpr hs),div_neg]
    have HR : ENNReal.ofReal (deriv u t) ≤ _ :=
      Hr.limsup_eq.symm.le.trans (limsup_le_limsup_of_le hrle)
    have HL : ENNReal.ofReal (-deriv u t) ≤ _ :=
      Hl.limsup_eq.symm.le.trans (limsup_le_limsup_of_le hlle)
    have HH := ascending_quotient_limsup_le hf γ t n
    rcases le_total 0 (deriv u t) with h | h
    · rw [abs_of_nonneg h]
      exact HR.trans HH
    · rw [abs_of_nonpos h]
      exact HL.trans HH
  · simp only [deriv_zero_of_not_differentiableAt hd,abs_zero,ENNReal.ofReal_zero]
    exact bot_le
lemma deriv_comp_le_ascendingSlope {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (hspeed : metricSpeed γ t ≠ ∞) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ascendingSlope f (evalReal γ t) * metricSpeed γ t := by
  rw [ascendingSlope_eq_iInf, ENNReal.iInf_mul (fun h => (hspeed h).elim)]
  exact le_iInf fun n => deriv_comp_le_ascendingSlopeApprox hf γ t n

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma ascendingSlope_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun x => (ascendingSlope f x).toReal) := by
  have hm : Measurable (fun x => (ascendingSlope f x).toReal) :=
    (measurable_ascendingSlope hf.continuous).ennreal_toReal
  have hbound : ∀ x, ‖(ascendingSlope f x).toReal‖ ≤ (L : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top (ascendingSlope_le hf x)).trans_eq
      (ENNReal.coe_toReal L)
  have hsl : ∀ x, ascendingSlope f x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (ascendingSlope_le hf x)
  refine ⟨?_, ae_of_all m fun _ => ENNReal.toReal_nonneg, ?_⟩
  · intro o R _hR
    let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ) (ae_of_all _ hbound)
  · intro π hπ _hb
    let : IsProbabilityMeasure π := hπ.1
    have hsm : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2 ^ 2) :=
      measurable_metricSpeed.pow_const 2
    have hfin := ae_lt_top hsm.lintegral_prod_right hπ.2.2.2.ne
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1, hfin] with γ hγ hfinγ
    have hfiniteSpeed : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), metricSpeed γ t ≠ ∞ := by
      have hh := ae_lt_top (hsm.comp measurable_prodMk_left) hfinγ.ne
      filter_upwards [hh] with t ht
      exact fun heq => by simp [heq] at ht
    have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
        simp [evalReal, clampTime, timeOne, timeZero]
        rfl
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hfiniteSpeed] with t ht
        simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_toReal (hsl _)]
          using deriv_comp_le_ascendingSlope hf γ t ht

lemma weakGradient_le_ascendingSlope (hfinite : FiniteOnBoundedSets m)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    ∀ᵐ x ∂m, weakGradient m u x ≤ (ascendingSlope u x).toReal := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m u D
  · exact (weakGradient_isMinimal h).2 _ (ascendingSlope_isLocalWeakUpperGradient hfinite hu)
  · simp only [weakGradient,dite_eq_right h,Pi.zero_apply]
    exact ae_of_all m fun _ => ENNReal.toReal_nonneg

omit [MeasurableSpace X] [BorelSpace X] in
lemma ascendingSlope_le_of_quadratic_increment {u : X → ℝ} {x : X} {a b : ℝ}
    (hu : ∀ z, u z-u x ≤ a*dist z x+b*dist z x^2) :
    ascendingSlope u x ≤ ENNReal.ofReal a := by
  rcases eq_or_ne (𝓝[≠] x) ⊥ with h | h
  · simp [ascendingSlope,h]
  have : NeBot (𝓝[≠] x) := ⟨h⟩
  have H : Tendsto (fun z => ENNReal.ofReal (a+b*dist z x)) (𝓝[≠] x)
      (𝓝 (ENNReal.ofReal a)) := by
    apply ENNReal.tendsto_ofReal
    have hc : Continuous (fun z : X => a+b*dist z x) := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds)
  calc
    ascendingSlope u x ≤ limsup (fun z => ENNReal.ofReal (a+b*dist z x)) (𝓝[≠] x) := by
      refine limsup_le_limsup ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (dist_pos.mpr hz)).mpr
      nlinarith [hu z]
    _ = _ := H.limsup_eq

omit [MeasurableSpace X] [BorelSpace X] in

lemma ascendingSlope_contact {φ ψ : X → ℝ} (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {x y : X} (hcontact : φ x+ψ y = dist x y^2/2) :
    ascendingSlope φ x ≤ ENNReal.ofReal (dist x y) := by
  apply ascendingSlope_le_of_quadratic_increment (b := 1/2)
  intro z
  have H := hdual z y
  have hd : dist z y^2 ≤ (dist z x+dist x y)^2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr (dist_triangle z x y)
  nlinarith

omit [MeasurableSpace X] [BorelSpace X] in

lemma contact_geodesic_decrease {φ ψ : X → ℝ}
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2) {γ : Curve X} (hγ : IsGeodesic γ)
    (hcontact : φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (t : Time) :
    t.val*(1-t.val/2)*dist (γ timeZero) (γ timeOne)^2 ≤ φ (γ timeZero)-φ (γ t) := by
  have H := hdual (γ t) (γ timeOne)
  have hd := hγ t timeOne
  have ht := t.property.2
  change dist (γ t) (γ timeOne) = |t.val - 1| * dist (γ timeZero) (γ timeOne) at hd
  rw [abs_of_nonpos (sub_nonpos.mpr ht)] at hd
  rw [hd] at H
  nlinarith

end WeakHessian

end
end InlinedFile0

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

lemma IsTestPlan.integrable_eval_bounded {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) {B : ℝ} (hB : ∀ᵐ x ∂m, |f x| ≤ B) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  let : IsProbabilityMeasure π := hπ.1
  exact (integrable_const B).mono' (hπ.aemeasurable_eval hf t).aestronglyMeasurable
    ((hπ.ae_eval_of_ae hB t).mono fun γ hγ => by simpa only [Real.norm_eq_abs] using hγ)

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

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsTestPlan.integrable_gradient_energy (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : Time) :
    Integrable (fun γ => (weakGradient m f (γ t))^2) π := by
  have hS := localSobolev_of_lipschitz hfin hf
  apply hπ.integrable_eval_bounded
    ((weakGradient_isMinimal hS.2).1.1.aestronglyMeasurable.pow 2).aemeasurable
    (B := (L:ℝ)^2)
  filter_upwards [weakGradient_nonneg (m := m) f,weakGradient_le_lipschitz hfin hf] with x hn hx
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ hn L.coe_nonneg).mpr hx

lemma IsTestPlan.integrable_gamma_eval (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f g : X → ℝ} {L T : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith T g) (t : Time) :
    Integrable (fun γ => gamma m f g (γ t)) π := by
  have hfS := localSobolev_of_lipschitz hfin hf
  have hgS := localSobolev_of_lipschitz hfin hg
  apply hπ.integrable_eval_bounded (gamma_aestronglyMeasurable hfin hfS hgS).aemeasurable (B := (L:ℝ)*T)
  filter_upwards [abs_gamma_le hfin hpar hfS hgS,weakGradient_le_lipschitz hfin hf,
    weakGradient_le_lipschitz hfin hg,weakGradient_nonneg (m := m) g] with x h hx hy hn
  exact h.trans (mul_le_mul hx hy hn L.coe_nonneg)

lemma IsTestPlan.perturbation_energy (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f g : X → ℝ} {L T : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith T g)
    (t : Time) (a : ℝ) :
    (∫ γ, (weakGradient m (fun x => f x+a*g x) (γ t))^2 ∂π) =
      (∫ γ, (weakGradient m f (γ t))^2 ∂π)+2*a*(∫ γ,gamma m f g (γ t) ∂π)+
      a^2*(∫ γ, (weakGradient m g (γ t))^2 ∂π) := by
  rw [integral_congr_ae (hπ.ae_eval_of_ae
    (weakGradient_linear_combination_sq hfin hpar
      (localSobolev_of_lipschitz hfin hf) (localSobolev_of_lipschitz hfin hg) a) t)]
  have hi1 := hπ.integrable_gradient_energy hfin hf t
  have hi2 := (hπ.integrable_gamma_eval hfin hpar hf hg t).const_mul (2*a)
  have hi3 := (hπ.integrable_gradient_energy hfin hg t).const_mul (a^2)
  have hi12 := hi1.add hi2
  change Integrable (fun γ => (weakGradient m f (γ t))^2+2*a*gamma m f g (γ t)) π at hi12
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,integral_const_mul]

lemma IsTestPlan.contact_gradient_energy_le (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ γ, (weakGradient m φ (γ timeZero))^2 ∂π) ≤ ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π := by
  let : IsProbabilityMeasure π := hπ.1
  apply integral_mono_ae (hπ.integrable_gradient_energy hfin hφ timeZero) hb.integrable_length_sq
  filter_upwards [hπ.ae_eval_of_ae (weakGradient_le_ascendingSlope hfin hφ) timeZero,
    hπ.ae_eval_of_ae (weakGradient_nonneg (m := m) φ) timeZero,hcontact] with γ hγ hn hc
  have H := (ENNReal.toReal_mono ENNReal.ofReal_ne_top (ascendingSlope_contact hdual hc)).trans_eq
    (ENNReal.toReal_ofReal dist_nonneg)
  exact (sq_le_sq₀ hn dist_nonneg).mpr (hγ.trans H)
end WeakHessian

namespace WeakHessianTransport
open Filter Set
open scoped Topology

lemma tendsto_of_quadratic_variations {ι : Type*} {l : Filter ι}
    {d : ι → ℝ} {B Q : ℝ}
    (h : ∀ a : ℝ, ∃ r : ι → ℝ, Tendsto r l (𝓝 (a*B+a^2*Q)) ∧
      ∀ᶠ i in l, a*d i ≤ r i) : Tendsto d l (𝓝 B) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let ε := δ/(2*(|Q|+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ε*|Q| < δ := by
    have H : |Q|/(2*(|Q|+1)) < 1 := (div_lt_one (by positivity)).mpr (by linarith [abs_nonneg Q])
    dsimp [ε]
    calc
      δ/(2*(|Q|+1))*|Q| = δ*(|Q|/(2*(|Q|+1))) := by ring
      _ < δ*1 := mul_lt_mul_of_pos_left H hδ
      _ = δ := mul_one _
  have heQ : ε^2*Q < ε*δ := by
    have H := mul_lt_mul_of_pos_left he hε
    have H' := mul_le_mul_of_nonneg_left (le_abs_self Q) (sq_nonneg ε)
    nlinarith
  obtain ⟨rp,hrp,hp⟩ := h ε
  obtain ⟨rn,hrn,hn⟩ := h (-ε)
  have ep := (tendsto_order.mp hrp).2 (ε*B+ε*δ) (by linarith)
  have en := (tendsto_order.mp hrn).2 (-ε*B+ε*δ) (by nlinarith)
  filter_upwards [ep,en,hp,hn] with i hip hin hip' hin'
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith
end WeakHessianTransport

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_VariationQuotient
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
open Filter Set MeasureTheory
open scoped Topology

lemma variation_quotient_le {a t A P C F I : ℝ} (ht : 0 < t) (hP : P ≤ A)
    (hC : t*(1-t/2)*A ≤ C) (hY : C+a*F ≤ (I+t*A)/2) :
    a*(F/t) ≤ ((I/t)-P+t*A)/2 := by
  have h : a*F ≤ (I-t*A+t^2*A)/2 := by nlinarith
  calc
    a*(F/t) = (a*F)/t := by ring
    _ ≤ ((I-t*A+t^2*A)/2)/t := div_le_div_of_nonneg_right h ht.le
    _ = ((I/t)-A+t*A)/2 := by field_simp [ne_of_gt ht]
    _ ≤ _ := by linarith
end WeakHessianTransport

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsTestPlan.contact_first_variation (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ f : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hf : LipschitzWith T f)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    Tendsto (fun t : ℝ => (∫ γ, f (γ timeZero)-f (evalReal γ t) ∂π)/t)
      (𝓝[>] 0) (𝓝 (∫ γ, gamma m φ f (γ timeZero) ∂π)) := by
  let : IsProbabilityMeasure π := hπ.1
  let A := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π
  let P := ∫ γ, (weakGradient m φ (γ timeZero))^2 ∂π
  let Q := (∫ γ, (weakGradient m f (γ timeZero))^2 ∂π)/2
  have hP : P ≤ A := hπ.contact_gradient_energy_le hfin hb hφ hdual hcontact
  apply WeakHessianTransport.tendsto_of_quadratic_variations (Q := Q)
  intro a
  let u : X → ℝ := fun x => φ x+a*f x
  have hu : LipschitzWith (L+‖a‖₊*T) u := hφ.add (lipschitz_const_mul_real hf a)
  let I : ℝ → ℝ := fun t => ∫ s in 0..t, ∫ γ, (weakGradient m u (evalReal γ s))^2 ∂π
  refine ⟨fun t => (I t/t-P+t*A)/2,?_,?_⟩
  · have H := ((hπ.tendsto_average_gradient_energy hfin hb hu).sub_const P).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).mul_const A)
    have HH := H.div_const (2:ℝ)
    have he : ((∫ γ, (weakGradient m u (γ timeZero))^2 ∂π)-P+0*A)/2 =
        a*(∫ γ, gamma m φ f (γ timeZero) ∂π)+a^2*Q := by
      dsimp only [u]
      rw [hπ.perturbation_energy hfin hpar hφ hf timeZero a]
      dsimp [P,Q]
      ring
    rw [he] at HH
    exact HH
  · have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < 1 := by
      have hgt : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
      have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
      exact hgt.and hlt
    filter_upwards [hevent] with t ht
    let τ : Time := ⟨t,ht.1.le,ht.2.le⟩
    have hc : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
    have hU := (weakGradient_isMinimal (localSobolev_of_lipschitz hfin hu).2).1
    have hUb : ∀ᵐ x ∂m, |weakGradient m u x| ≤ ((L+‖a‖₊*T : ℝ≥0):ℝ) := by
      filter_upwards [weakGradient_nonneg (m := m) u,weakGradient_le_lipschitz hfin hu] with x hn hx
      simpa only [abs_of_nonneg hn] using hx
    have hY := hU.geodesic_young_time hu.continuous.aemeasurable (L+‖a‖₊*T).coe_nonneg hUb hπ hb hgeo τ ht.1
    have hiφ (s : Time) := hb.integrable_lipschitz_eval hφ s
    have hif (s : Time) := hb.integrable_lipschitz_eval hf s
    have hcomb : (∫ γ, u (γ timeZero)-u (γ τ) ∂π) =
        (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π)+a*(∫ γ, f (γ timeZero)-f (γ τ) ∂π) := by
      have H : (fun γ : Curve X => u (γ timeZero)-u (γ τ)) =
          fun γ => (φ (γ timeZero)-φ (γ τ))+a*(f (γ timeZero)-f (γ τ)) := by
        funext γ; dsimp [u]; ring
      have hi1 := (hiφ timeZero).sub (hiφ τ)
      have hi2 := ((hif timeZero).sub (hif τ)).const_mul a
      change Integrable (fun γ => φ (γ timeZero)-φ (γ τ)) π at hi1
      change Integrable (fun γ => a*(f (γ timeZero)-f (γ τ))) π at hi2
      rw [H,integral_add hi1 hi2,integral_const_mul]
    rw [hcomb] at hY
    have hC : t*(1-t/2)*A ≤ (∫ γ, φ (γ timeZero)-φ (γ τ) ∂π) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hb.integrable_length_sq.const_mul _) ((hiφ timeZero).sub (hiφ τ))
      filter_upwards [hgeo,hcontact] with γ hγ hg
      exact contact_geodesic_decrease hdual hγ hg τ
    have H := WeakHessianTransport.variation_quotient_le ht.1 hP hC hY
    simpa only [I,τ,evalReal,hc] using H
end WeakHessian

end
end InlinedFile0

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
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ScalarEntropyLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile2
noncomputable section
namespace WeakHessianEntropyScalar

lemma log_floor_difference_mono {a b u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.log (u+b)-Real.log (u+a) ≤ Real.log (v+b)-Real.log (v+a) := by
  have ha : 0 < a := hb.trans_le hba
  have hv : 0 ≤ v := hu.trans huv
  rw [← Real.log_div (by positivity) (by positivity),
    ← Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr huv)]

lemma log_floor_comparison_good {a b d u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hd : 0 ≤ d) (hu : 0 < u) (hu2 : 2*d ≤ u) (hvu : u-d ≤ v) :
    u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) ≥ -2*a*d := by
  have ha : 0 < a := hb.trans_le hba
  have hv : 0 < v := by linarith
  by_cases huv : u ≤ v
  · have H := log_floor_difference_mono hb hba hu.le huv
    have J : 0 ≤ u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [mul_nonneg ha.le hd]
  have hvu' : v ≤ u := le_of_not_ge huv
  let E := (u+a)*(v+b)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE2 : u^2 ≤ 2*E := by
    have H : u^2 ≤ 2*(u*v) := by nlinarith
    have J : u*v ≤ E := by dsimp [E]; nlinarith [mul_nonneg hu.le hb.le,mul_nonneg ha.le hv.le,mul_nonneg ha.le hb.le]
    linarith
  have hn : (a-b)*(u-v) ≤ a*d := by
    calc
      _ ≤ a*(u-v) := by gcongr; linarith
      _ ≤ a*d := by gcongr; linarith
  have heq : (u+b)*(v+a)/E-1 = (a-b)*(u-v)/E := by
    dsimp only [E]
    field_simp
    ring
  have hR : 0 < (u+b)*(v+a)/E := by positivity
  have hlog := Real.log_le_sub_one_of_pos hR
  rw [Real.log_div (by positivity) hE.ne',Real.log_mul (by positivity) (by positivity),
    show Real.log E = Real.log (u+a)+Real.log (v+b) by
      dsimp [E]; rw [Real.log_mul (by positivity) (by positivity)],heq] at hlog
  have H : u^2*((a-b)*(u-v)/E) ≤ 2*a*d := by
    rw [← mul_div_assoc,div_le_iff₀ hE]
    calc
      u^2*((a-b)*(u-v)) ≤ u^2*(a*d) := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ ≤ (2*E)*(a*d) := mul_le_mul_of_nonneg_right hE2 (mul_nonneg ha.le hd)
      _ = 2*a*d*E := by ring
  have J := mul_le_mul_of_nonneg_left hlog (sq_nonneg u)
  nlinarith

lemma log_floor_comparison {a b d u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v) (hvu : u-d ≤ v) :
    u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) ≥
      -2*a*d-4*d^2*Real.log ((2*d+b)/b) := by
  have ha : 0 < a := hb.trans_le hba
  have hr : 1 ≤ (2*d+b)/b := by rw [le_div_iff₀ hb]; linarith
  have hl := Real.log_nonneg hr
  by_cases hu2 : 2*d ≤ u
  · by_cases hu0 : u = 0
    · subst u
      have hd0 : d = 0 := by linarith
      simp [hd0]
    · have H := log_floor_comparison_good hb hba hd (lt_of_le_of_ne hu (Ne.symm hu0)) hu2 hvu
      nlinarith [mul_nonneg (sq_nonneg d) hl]
  have hu2' : u ≤ 2*d := le_of_not_ge hu2
  have H := log_floor_difference_mono hb hba (by norm_num : (0:ℝ) ≤ 0) hv
  simp only [zero_add] at H
  have J := Real.log_le_log ha (show a ≤ u+a by linarith)
  have I := Real.log_le_log (show 0 < u+b by positivity) (show u+b ≤ 2*d+b by linarith)
  have B : -(Real.log ((2*d+b)/b)) ≤
      Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a) := by
    rw [Real.log_div (by positivity) hb.ne']
    linarith
  have han : 0 ≤ 2*a*d := by positivity
  have H1 := mul_le_mul_of_nonneg_left B (sq_nonneg u)
  have H2 : u^2*Real.log ((2*d+b)/b) ≤ 4*d^2*Real.log ((2*d+b)/b) := by
    gcongr
    nlinarith
  nlinarith
open Filter Set
open scoped Topology

lemma tendsto_time_log_reciprocal {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun t : ℝ => t*Real.log (1+c/t)) (𝓝[>] 0) (𝓝 0) := by
  rcases hc.eq_or_lt with h|h
  · subst c
    simp
  have H : Tendsto (fun t : ℝ => t*Real.log (t+c)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht.mul ((Real.continuousAt_log h.ne').tendsto.comp
      (by simpa using ht.add_const c))
  have J : Tendsto (fun t : ℝ => t*Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  convert (H.sub J).congr' ?_ using 1
  · norm_num
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have heq : 1+c/t = (t+c)/t := by field_simp
    rw [heq,Real.log_div (by positivity) ht.ne']
    ring

end WeakHessianEntropyScalar

end
end InlinedFile2

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TruncatedLog
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
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal

lemma truncatedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (truncatedLog a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (truncatedLog_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (truncatedLog a) = (fun x => (max a x)⁻¹) from funext (truncatedLog_deriv ha)]
  exact (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))

lemma truncatedLog_eq {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    truncatedLog a x = Real.log x := by
  have H : (∫ s in a..x, (max a s)⁻¹) = Real.log x-Real.log a := by
    calc
      (∫ s in a..x, (max a s)⁻¹) = ∫ s in a..x, s⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hax] at hs
        exact congrArg Inv.inv (max_eq_right hs.1)
      _ = Real.log x-Real.log a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          rw [uIcc_of_le hax] at hs
          exact Real.hasDerivAt_log (ne_of_gt (ha.trans_le hs.1))
        · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt (ha.trans_le hs.1))).intervalIntegrable_of_Icc hax
  dsimp only [truncatedLog]
  rw [H]
  ring

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedLog a) ((max a (x+a))⁻¹) x := by
  simpa only [regularizedLog,Function.comp_def,mul_one] using!
    ((truncatedLog_hasDeriv ha (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub_const (Real.log a)
lemma regularizedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedLog a) x = (max a (x+a))⁻¹ := (regularizedLog_hasDeriv ha x).deriv
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]
lemma regularizedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedLog a) x| ≤ a⁻¹ := by
  rw [regularizedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a (x+a))))]
  exact inv_anti₀ ha (le_max_left _ _)

end WeakHessian

end
end InlinedFile0

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
lemma squareDensity_integrable {n : Measure X} {w f : X → ℝ} (hw : Measurable w) :
    Integrable f (squareDensityMeasure n w) ↔ Integrable (fun x => w x^2*f x) n := by
  rw [squareDensityMeasure,integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_inv_integrable {n : Measure X} [IsFiniteMeasure n] {w : X → ℝ}
    (hw : Measurable w) : Integrable (fun x => (w x^2)⁻¹) (squareDensityMeasure n w) := by
  rw [squareDensity_integrable hw]
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ fun x => by
    by_cases h : w x^2 = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_inv_mass {n : Measure X} [IsFiniteMeasure n] {w : X → ℝ}
    (hw : Measurable w) :
    (∫ x, (w x^2)⁻¹ ∂squareDensityMeasure n w) ≤ n.real univ := by
  rw [squareDensity_integral hw]
  have H := integral_mono ((squareDensity_integrable hw).mp (squareDensity_inv_integrable hw))
    (integrable_const (1:ℝ) (μ := n)) (fun x => show w x^2*(w x^2)⁻¹ ≤ 1 by
      by_cases h : w x^2 = 0
      · simp [h]
      · simp [mul_inv_cancel₀ h])
  simpa using H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_pos_ae {n : Measure X} {w : X → ℝ}
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) :
    ∀ᵐ x ∂squareDensityMeasure n w, 0 < w x := by
  apply (ae_withDensity_iff (by fun_prop)).mpr
  exact ae_of_all _ fun x hx => by
    have hs : w x^2 ≠ 0 := fun h => hx (by simp [h])
    exact lt_of_le_of_ne (hn x) (fun h => hs (by simp [← h]))

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma squareLogFloor_eq {a : ℝ} (ha : 0 < a) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (x : X) :
    squareLogFloor a w x = 2*Real.log (w x+a) := by
  simp only [squareLogFloor,regularizedLog_eq ha (hw x),sub_add_cancel]

omit [MeasurableSpace X] [BorelSpace X] in
lemma squareLogFloor_lipschitz {a : ℝ} (ha : 0 < a) {w : X → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) :
    LipschitzWith (‖(2:ℝ)‖₊*(Real.toNNReal a⁻¹*L)) (squareLogFloor a w) := by
  have H : LipschitzWith (Real.toNNReal a⁻¹*L) (fun x => regularizedLog a (w x)+Real.log a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have H := ((regularizedLog_lipschitz ha).comp hw).dist_le_mul x y
    change dist (regularizedLog a (w x)) (regularizedLog a (w y)) ≤ a⁻¹*(L:ℝ)*dist x y at H
    simpa only [dist_add_right,NNReal.coe_mul,Real.coe_toNNReal _ (inv_nonneg.mpr ha.le)] using H
  exact lipschitz_const_mul_real H 2

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exp_squareLogFloor {a : ℝ} (ha : 0 < a) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (x : X) :
    Real.exp (squareLogFloor a w x) = (w x+a)^2 := by
  rw [squareLogFloor_eq ha hw,two_mul,Real.exp_add,Real.exp_log (add_pos_of_nonneg_of_pos (hw x) ha),pow_two]

lemma squareDensity_entropy_upper {n : Measure X} [IsFiniteMeasure n] (w : X →ᵇ ℝ)
    [IsFiniteMeasure (squareDensityMeasure n w)] (hw : ∀ x, 0 ≤ w x) {a : ℝ} (ha : 0 < a) :
    entropyReal n (squareDensityMeasure n w) ≤
      ∫ x, squareLogFloor a w x ∂squareDensityMeasure n w := by
  have habs : squareDensityMeasure n w ≪ n := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density habs,squareDensity_integral w.continuous.measurable]
  have hrn := Measure.rnDeriv_withDensity n (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)
  have heq : (fun x => ((squareDensityMeasure n w).rnDeriv n x).toReal *
      Real.log ((squareDensityMeasure n w).rnDeriv n x).toReal) =ᵐ[n]
      fun x => w x^2*Real.log (w x^2) := by
    filter_upwards [hrn] with x hx
    simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [integral_congr_ae heq]
  have hi : Integrable (fun x => w x^2*Real.log (w x^2)) n := by
    have H : Continuous (fun x : X => w x^2*Real.log (w x^2)) :=
      Real.continuous_mul_log.comp (w.continuous.pow 2)
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := ‖w‖^2)).exists_bound_of_continuousOn
      (f := fun r : ℝ => r*Real.log r) Real.continuous_mul_log.continuousOn
    apply Integrable.of_bound H.aestronglyMeasurable C
    refine ae_of_all _ fun x => hC _ ⟨sq_nonneg _,?_⟩
    have H := w.norm_coe_le_norm x
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) H 2
  have hi2 := (squareDensity_integrable (n := n) w.continuous.measurable).mp ((squareLogFloorBCF ha w).integrable _)
  apply integral_mono hi hi2
  intro x
  by_cases hx : w x = 0
  · simp [hx]
  have hx0 : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
  change w x^2*Real.log (w x^2) ≤ w x^2*squareLogFloor a w x
  rw [squareLogFloor_eq ha hw,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx0 (by linarith)) (by norm_num)) (sq_nonneg _)

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_mass {n : Measure X} {w : X → ℝ} (hw : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure n w)] : (∫ x, w x^2 ∂n) = 1 := by
  have H := squareDensity_integral (n := n) hw (fun _ => (1:ℝ))
  simpa using H.symm

lemma squareDensity_fenchel_defect {n μ : Measure X} [IsFiniteMeasure n]
    [IsProbabilityMeasure μ] (w : X →ᵇ ℝ) [IsProbabilityMeasure (squareDensityMeasure n w)]
    (hw : ∀ x, 0 ≤ w x) (hμ : FiniteEntropy n μ) {a : ℝ} (ha : 0 < a) :
    entropyReal n (squareDensityMeasure n w)-entropyReal n μ ≤
      (∫ x, squareLogFloor a w x ∂squareDensityMeasure n w)-
      (∫ x, squareLogFloor a w x ∂μ)+2*a*(∫ x,w x ∂n)+a^2*n.real univ := by
  have hu := squareDensity_entropy_upper (n := n) w hw ha
  have hl := entropyReal_fenchel hμ (squareLogFloorBCF ha w)
  have he : (∫ x, Real.exp (squareLogFloorBCF ha w x) ∂n) =
      1+2*a*(∫ x, w x ∂n)+a^2*n.real univ := by
    simp only [squareLogFloorBCF_apply,exp_squareLogFloor ha hw]
    have hf : (fun x => (w x+a)^2) = fun x => w x^2+(2*a)*w x+a^2 := by funext x; ring
    have hi : Integrable (fun x => w x^2) n := (w^2).integrable n
    rw [hf,integral_add (f := fun x => w x^2+(2*a)*w x) (g := fun _ => a^2)
      (hi.add ((w.integrable n).const_mul (2*a))) (integrable_const _),
      integral_add (f := fun x => w x^2) (g := fun x => (2*a)*w x) hi ((w.integrable n).const_mul (2*a)),integral_const_mul,
      squareDensity_mass w.continuous.measurable,integral_const,smul_eq_mul]
    ring
  simp only [squareLogFloorBCF_apply,Measure.real,measure_univ,ENNReal.toReal_one] at hl
  rw [show (∫ x,Real.exp (squareLogFloor a w x) ∂n) = _ from he] at hl
  linarith

lemma squareLogFloor_increment_comparison {Z : Type*} [MeasurableSpace Z]
    {π : Measure Z} [IsFiniteMeasure π] {n : Measure X} [IsFiniteMeasure n]
    {s r : Z → X} (hs : AEMeasurable s π) (hr : AEMeasurable r π)
    (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (h0 : π.map s = squareDensityMeasure n w)
    {a b d : ℝ} (hb : 0 < b) (hba : b ≤ a) (hd : 0 ≤ d)
    (hmove : ∀ᵐ z ∂π, w (s z)-d ≤ w (r z)) :
    (∫ z, squareLogFloor b w (s z)-squareLogFloor b w (r z) ∂π) ≤
      (∫ z, squareLogFloor a w (s z)-squareLogFloor a w (r z) ∂π)+
      (4*a*d+8*d^2*Real.log ((2*d+b)/b))*n.real univ := by
  have ha := hb.trans_le hba
  have hip : Integrable (fun z => (w (s z)^2)⁻¹) π := by
    apply (integrable_map_measure (g := fun x => (w x^2)⁻¹) (by fun_prop) hs).mp
    rw [h0]
    exact squareDensity_inv_integrable w.continuous.measurable
  have hmass : (∫ z, (w (s z)^2)⁻¹ ∂π) ≤ n.real univ := by
    rw [← integral_map (f := fun x => (w x^2)⁻¹) hs (by fun_prop),h0]
    exact squareDensity_inv_mass w.continuous.measurable
  have hp : ∀ᵐ z ∂π, 0 < w (s z) := by
    apply ae_of_ae_map hs (p := fun x => 0 < w x)
    rw [h0]
    exact squareDensity_pos_ae w.continuous.measurable hw
  let C := 4*a*d+8*d^2*Real.log ((2*d+b)/b)
  have hC : 0 ≤ C := by
    have hR : 1 ≤ (2*d+b)/b := by rw [le_div_iff₀ hb]; linarith
    have hlog := Real.log_nonneg hR
    dsimp [C]
    positivity
  have his (c : ℝ) (hc : 0 < c) : Integrable (fun z => squareLogFloor c w (s z)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hc w).continuous.aestronglyMeasurable hs).mp
      ((squareLogFloorBCF hc w).integrable _)
  have hir (c : ℝ) (hc : 0 < c) : Integrable (fun z => squareLogFloor c w (r z)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hc w).continuous.aestronglyMeasurable hr).mp
      ((squareLogFloorBCF hc w).integrable _)
  have H := integral_mono_ae ((his b hb).sub (hir b hb))
    (((his a ha).sub (hir a ha)).add (hip.const_mul C)) (show ∀ᵐ z ∂π,
      squareLogFloor b w (s z)-squareLogFloor b w (r z) ≤
      (squareLogFloor a w (s z)-squareLogFloor a w (r z))+C*(w (s z)^2)⁻¹ from by
    filter_upwards [hp,hmove] with z hz hzm
    have H := WeakHessianEntropyScalar.log_floor_comparison hb hba hd (hw (s z)) (hw (r z)) hzm
    simp only [squareLogFloor_eq hb hw,squareLogFloor_eq ha hw]
    have hz2 : 0 < w (s z)^2 := sq_pos_of_pos hz
    have hh : (2*Real.log (w (s z)+b)-2*Real.log (w (r z)+b))-
        (2*Real.log (w (s z)+a)-2*Real.log (w (r z)+a)) ≤ C/(w (s z)^2) := by
      rw [le_div_iff₀ hz2]
      dsimp [C]
      nlinarith
    simpa only [div_eq_mul_inv,add_comm] using (sub_le_iff_le_add.mp hh))
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun z => squareLogFloor a w (s z)-squareLogFloor a w (r z))
    (g := fun z => C*(w (s z)^2)⁻¹) ((his a ha).sub (hir a ha)) (hip.const_mul C),integral_const_mul] at H
  exact H.trans (by dsimp only [C] at *; linarith [mul_le_mul_of_nonneg_left hmass hC])

lemma entropy_chord_squareRoot_approx {π : Measure (Curve X)} [IsProbabilityMeasure π]
    {n : Measure X} [IsFiniteMeasure n] (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x)
    (h0 : interpolation π timeZero = squareDensityMeasure n w)
    {K A c : ℝ} (hc : 0 ≤ c)
    (hmove : ∀ t : Time, ∀ᵐ γ ∂π, w (γ timeZero)-c*(t:ℝ) ≤ w (γ t))
    (hcurv : ∀ t : Time, FiniteEntropy n (interpolation π t) ∧
      entropyReal n (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal n (interpolation π timeZero)+
          (t:ℝ)*entropyReal n (interpolation π timeOne)-K/2*(t:ℝ)*(1-(t:ℝ))*A)
    {a D : ℝ} (ha : 0 < a)
    (hd : Tendsto (fun t : ℝ => (∫ γ, squareLogFloor a w (γ timeZero)-
      squareLogFloor a w (evalReal γ t) ∂π)/t) (𝓝[>] 0) (𝓝 D)) :
    entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+K/2*A ≤
      D+4*a*c*n.real univ := by
  let E := entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)
  let M := n.real univ
  let W := ∫ x,w x ∂n
  let I (a t : ℝ) := (∫ γ, squareLogFloor a w (γ timeZero)-squareLogFloor a w (evalReal γ t) ∂π)
  let : IsProbabilityMeasure (squareDensityMeasure n w) := by
    rw [← h0]
    exact interpolation_probability π timeZero
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq : ∀ᶠ t : ℝ in 𝓝[>] 0, t^2 < a := by
    exact (ht0.pow 2).eventually (gt_mem_nhds (by simpa using ha))
  have hl : Tendsto (fun t : ℝ => E+K/2*(1-t)*A) (𝓝[>] 0) (𝓝 (E+K/2*A)) := by
    simpa using (tendsto_const_nhds (x := E)).add ((((tendsto_const_nhds (x := (1:ℝ))).sub ht0).const_mul (K/2)).mul_const A)
  have hr : Tendsto (fun t : ℝ => I a t/t+4*a*c*M+
      8*c^2*M*(t*Real.log (1+2*c/t))+2*t*W+t^3*M)
      (𝓝[>] 0) (𝓝 (D+4*a*c*M)) := by
    have hlog := WeakHessianEntropyScalar.tendsto_time_log_reciprocal (show 0 ≤ 2*c by positivity)
    have HH := (((hd.add_const (4*a*c*M)).add (hlog.const_mul (8*c^2*M))).add
      ((ht0.const_mul 2).mul_const W)).add ((ht0.pow 3).mul_const M)
    simpa only [I,mul_zero,zero_mul,zero_pow (by norm_num : (3:ℕ) ≠ 0),add_zero] using HH
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [hsq,show ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0:ℝ) 1 from Ioo_mem_nhdsGT zero_lt_one] with t hta ht
  let τ : Time := ⟨t,ht.1.le,ht.2.le⟩
  have hcl : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
  have hmap (b : ℝ) (hb : 0 < b) (s : Time) :
      (∫ x, squareLogFloor b w x ∂interpolation π s) = ∫ γ,squareLogFloor b w (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable (squareLogFloorBCF hb w).continuous.aestronglyMeasurable
  have hit (b : ℝ) (hb : 0 < b) (s : Time) : Integrable (fun γ => squareLogFloor b w (γ s)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hb w).continuous.aestronglyMeasurable
      (continuous_eval_const s).measurable.aemeasurable).mp ((squareLogFloorBCF hb w).integrable _)
  have ht2 : 0 < t^2 := sq_pos_of_pos ht.1
  let : IsProbabilityMeasure (interpolation π τ) := interpolation_probability π τ
  have hfen := squareDensity_fenchel_defect w hw (hcurv τ).1 ht2
  rw [← h0,hmap _ ht2 timeZero,hmap _ ht2 τ,← integral_sub (hit _ ht2 timeZero) (hit _ ht2 τ)] at hfen
  have hcomp := squareLogFloor_increment_comparison
    (continuous_eval_const timeZero).measurable.aemeasurable
    (continuous_eval_const τ).measurable.aemeasurable w hw h0 ht2 hta.le (mul_nonneg hc ht.1.le) (hmove τ)
  have he : ((2*(c*t)+t^2)/t^2) = 1+2*c/t := by field_simp [ht.1.ne']; ring
  have hnum : t*(E+K/2*(1-t)*A) ≤ I a t+
      (4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M := by
    have H := (hcurv τ).2
    change entropyReal n (interpolation π τ) ≤ (1-t)*entropyReal n (interpolation π timeZero)+
      t*entropyReal n (interpolation π timeOne)-K/2*t*(1-t)*A at H
    have heI : (∫ γ, squareLogFloor a w (γ timeZero)-squareLogFloor a w (γ τ) ∂π) = I a t := by
      simp only [I,evalReal,hcl]
    rw [heI,he] at hcomp
    dsimp only [E,M,W]
    nlinarith
  have hdiv : E+K/2*(1-t)*A ≤
      (I a t+(4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M)/t := by
    rw [le_div_iff₀ ht.1]
    nlinarith [hnum]
  have halg : (I a t+(4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M)/t =
      I a t/t+4*a*c*M+8*c^2*M*(t*Real.log (1+2*c/t))+2*t*W+t^3*M := by
    field_simp [ht.1.ne']
    ring
  rw [halg] at hdiv
  exact hdiv

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_squareLogFloor (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {φ w : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T w)
    (hn : ∀ x, 0 ≤ w x) {a : ℝ} (ha : 0 < a) :
    gamma m φ (squareLogFloor a w) =ᵐ[m] fun x => 2/(w x+a)*gamma m φ w x := by
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  have hrL := (regularizedLog_lipschitz ha).comp hw
  have hrS := localSobolev_of_lipschitz hfin hrL
  have hchain := gamma_comp_contDiff hfin hpar hwS hφS (regularizedLog_contDiff ha)
    hrS.1 (ae_of_all _ fun x => regularizedLog_deriv_bound ha (w x))
  filter_upwards [gamma_comm (m := m) φ (squareLogFloor a w),
    gamma_const_mul_left hfin hpar (hrS.add_const hfin (Real.log a)) hφS 2,
    gamma_add_const_left hfin hrS hφS (Real.log a),hchain,gamma_comm (m := m) w φ] with x hc hm ha' hh hs
  change gamma m (squareLogFloor a w) φ x = 2*gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x at hm
  change gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x = gamma m (regularizedLog a ∘ w) φ x at ha'
  rw [hc,hm,ha',hh,hs,regularizedLog_deriv ha,max_eq_right (by linarith [hn x])]
  simp only [div_eq_mul_inv]
  ring

lemma integrable_local_gamma_finite_ac (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    {φ w : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T w) :
    Integrable (gamma m φ w) n := by
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  apply Integrable.of_bound ((gamma_aestronglyMeasurable hfin hφS hwS).mono_ac hn) ((L:ℝ)*T)
  apply hn.ae_le
  filter_upwards [abs_gamma_le hfin hpar hφS hwS,weakGradient_le_lipschitz hfin hφ,
    weakGradient_le_lipschitz hfin hw,weakGradient_nonneg (m := m) w] with x h hx hy hn
  rw [Real.norm_eq_abs]
  exact h.trans (mul_le_mul hx hy hn L.coe_nonneg)

lemma squareLogFloor_contact_upper (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (w : X →ᵇ ℝ) {φ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T (w: X → ℝ))
    (hwn : ∀ x, 0 ≤ w x) (h0 : interpolation π timeZero = squareDensityMeasure n w)
    {a : ℝ} (ha : 0 < a) :
    (∫ γ, gamma m φ (squareLogFloor a w) (γ timeZero) ∂π) ≤
      (∫ x, 2*w x*gamma m φ w x ∂n)+2*a*(∫ x,|gamma m φ w x| ∂n) := by
  let : IsProbabilityMeasure π := hπ.1
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  have hfl := squareLogFloor_lipschitz ha hw
  have hfS := localSobolev_of_lipschitz hfin hfl
  have hgm := gamma_aestronglyMeasurable hfin hφS hfS
  have hG := integrable_local_gamma_finite_ac hfin hpar hn hφ hw
  have hGm := (gamma_aestronglyMeasurable hfin hφS hwS).mono_ac hn
  have hΓ : Integrable (fun x => 2*w x*gamma m φ w x) n := by
    apply (hG.norm.const_mul (2*‖w‖)).mono' ((w.continuous.aestronglyMeasurable.const_mul 2).mul hGm)
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have H := w.norm_coe_le_norm x
    norm_num only [Real.norm_eq_abs] at H
    nlinarith [mul_le_mul_of_nonneg_right H (abs_nonneg (gamma m φ w x))]
  have hinit : interpolation π timeZero ≪ m := (hπ.2.1.choose_spec timeZero).absolutelyContinuous.trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have him : Integrable (gamma m φ (squareLogFloor a w)) (squareDensityMeasure n w) := by
    rw [← h0]
    exact (integrable_map_measure (hgm.mono_ac hinit) (continuous_eval_const timeZero).measurable.aemeasurable).mpr
      (hπ.integrable_gamma_eval hfin hpar hφ hfl timeZero)
  rw [← integral_map (continuous_eval_const timeZero).measurable.aemeasurable (hgm.mono_ac hinit)]
  change (∫ x, gamma m φ (squareLogFloor a w) x ∂interpolation π timeZero) ≤ _
  rw [h0,squareDensity_integral hw.continuous.measurable]
  have hchain := hn.ae_eq (gamma_squareLogFloor hfin hpar hφ hw hwn ha)
  have hI := (squareDensity_integrable hw.continuous.measurable).mp him
  have H := integral_mono_ae hI (hΓ.add (hG.abs.const_mul (2*a))) (show ∀ᵐ x ∂n,
    w x^2*gamma m φ (squareLogFloor a w) x ≤ 2*w x*gamma m φ w x+2*a*|gamma m φ w x| from by
    filter_upwards [hchain] with x hx
    rw [hx]
    have hp : 0 < w x+a := add_pos_of_nonneg_of_pos (hwn x) ha
    have hwdiv : 0 ≤ w x/(w x+a) := div_nonneg (hwn x) hp.le
    have hwle : w x/(w x+a) ≤ 1 := by rw [div_le_one hp]; linarith
    have H := neg_abs_le (gamma m φ w x)
    have HH : -(2*a)*(w x/(w x+a))*gamma m φ w x ≤ 2*a*|gamma m φ w x| := by
      calc
        _ ≤ (2*a)*(w x/(w x+a))*|gamma m φ w x| := by nlinarith [mul_nonneg (by positivity : 0 ≤ (2*a)*(w x/(w x+a))) (by linarith : 0 ≤ gamma m φ w x+|gamma m φ w x|)]
        _ ≤ 2*a*|gamma m φ w x| := by nlinarith [mul_le_mul_of_nonneg_right hwle (by positivity : 0 ≤ 2*a*|gamma m φ w x|)]
    have he : w x^2*(2/(w x+a)*gamma m φ w x)-2*w x*gamma m φ w x =
        -(2*a)*(w x/(w x+a))*gamma m φ w x := by field_simp [hp.ne']; ring
    rw [← he] at HH
    linarith)
  simp only [Pi.add_apply] at H
  rw [integral_add (f := fun x => 2*w x*gamma m φ w x) (g := fun x => 2*a*|gamma m φ w x|)
    hΓ (hG.abs.const_mul (2*a)),integral_const_mul] at H
  exact H

lemma IsTestPlan.entropy_squareRoot_subdifferential (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    (w : X →ᵇ ℝ) {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ)
    (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h0 : interpolation π timeZero = squareDensityMeasure n w) {K : ℝ}
    (hcurv : ∀ t : Time, FiniteEntropy n (interpolation π t) ∧
      entropyReal n (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal n (interpolation π timeZero)+
          (t:ℝ)*entropyReal n (interpolation π timeOne)-
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)) :
    entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+
      K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤
      ∫ x,2*w x*gamma m φ w x ∂n := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨o,R,hR,htracks⟩ := hb
  let c : ℝ := (T:ℝ)*(2*R)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmove (t : Time) : ∀ᵐ γ ∂π, w (γ timeZero)-c*(t:ℝ) ≤ w (γ t) := by
    filter_upwards [hgeo,htracks] with γ hγ ht
    have hl : dist (γ timeZero) (γ timeOne) ≤ 2*R := by
      have H := dist_triangle (γ timeZero) o (γ timeOne)
      rw [dist_comm o] at H
      linarith [ht timeZero,ht timeOne]
    have Hd : dist (γ timeZero) (γ t) = (t:ℝ)*dist (γ timeZero) (γ timeOne) := by
      rw [hγ timeZero t]
      simp only [timeZero,zero_sub,abs_neg,abs_of_nonneg t.2.1]
    have H := hw.le_add_mul (γ timeZero) (γ t)
    rw [Hd] at H
    have J := mul_le_mul_of_nonneg_left hl (mul_nonneg T.coe_nonneg t.2.1)
    dsimp only [c]
    nlinarith
  let G := ∫ x,2*w x*gamma m φ w x ∂n
  let C := (2*(∫ x,|gamma m φ w x| ∂n)+4*c*n.real univ)
  have hall (a : ℝ) (ha : 0 < a) :
      entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+
        K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤ G+a*C := by
    have hd := hπ.contact_first_variation hfin hpar ⟨o,R,hR,htracks⟩ hgeo hφ
      (squareLogFloor_lipschitz ha hw) hdual hcontact
    have H := entropy_chord_squareRoot_approx w hwn h0 hc hmove hcurv ha hd
    have J := squareLogFloor_contact_upper hfin hpar hn hπ w hφ hw hwn h0 ha
    dsimp only [G,C]
    nlinarith
  have hlim : Tendsto (fun a : ℝ => G+a*C) (𝓝[>] 0) (𝓝 G) := by
    simpa using (tendsto_const_nhds (x := G)).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0)).mul_const C)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact hall a ha

end WeakHessian

end
end InlinedFile3

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Subdifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile4
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_restrict {m : Measure X} {w : X → ℝ} {Q : Set X}
    (hQ : MeasurableSet Q) (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    squareDensityMeasure (m.restrict Q) w = squareDensityMeasure m w := by
  change (m.restrict Q).withDensity _ = squareDensityMeasure m w
  rw [← restrict_withDensity hQ]
  exact Measure.restrict_eq_self_of_ae_mem hs

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_support_integral {m : Measure X} {w f : X → ℝ}
    (hw : Measurable w) {Q : Set X} (hQ : MeasurableSet Q)
    (hs : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q) :
    (∫ x, w x*f x ∂m.restrict Q) = ∫ x, w x*f x ∂m := by
  have H := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp hs
  rw [← integral_indicator hQ]
  apply integral_congr_ae
  filter_upwards [H] with x hx
  by_cases h : x ∈ Q
  · simp only [indicator_of_mem h]
  · have he : ENNReal.ofReal (w x^2) = 0 := not_not.mp (mt hx h)
    have hz : w x = 0 := by
      have H := ENNReal.ofReal_eq_zero.mp he
      nlinarith [sq_nonneg (w x)]
    simp only [indicator_of_notMem h,hz,zero_mul]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsTestPlan.entropy_squareRoot_subdifferential_original {m : Measure X} [SigmaFinite m]
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (w : X →ᵇ ℝ) {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ)
    (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h0 : interpolation π timeZero = squareDensityMeasure m w) {K : ℝ}
    (hcurv : ∀ t : Time, FiniteEntropy m (interpolation π t) ∧
      entropyReal m (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal m (interpolation π timeZero)+
          (t:ℝ)*entropyReal m (interpolation π timeOne)-
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)) :
    entropyReal m (interpolation π timeZero)-entropyReal m (interpolation π timeOne)+
      K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤
      ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure π := hπ.1
  let (t : Time) : IsProbabilityMeasure (interpolation π t) := interpolation_probability π t
  obtain ⟨o,R,hR,htracks⟩ := hb
  let Q := Metric.closedBall o R
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  have hs (t : Time) : ∀ᵐ x ∂interpolation π t, x ∈ Q := by
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hQ).mpr
    exact htracks.mono fun γ hγ => hγ t
  let n := m.restrict Q
  let : IsFiniteMeasure n := ⟨by
    simpa only [n,Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have he (t : Time) : entropyReal n (interpolation π t) = entropyReal m (interpolation π t) :=
    entropyReal_restrict_reference hQ (hcurv t).1.1 (hs t)
  simp only [n] at he
  have h0s : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q := by rw [← h0]; exact hs timeZero
  have h0n : interpolation π timeZero = squareDensityMeasure n w := by
    rw [h0,show squareDensityMeasure n w = squareDensityMeasure m w from squareDensity_restrict hQ h0s]
  have H := hπ.entropy_squareRoot_subdifferential hfin hpar ⟨o,R,hR,htracks⟩ hgeo
    (Measure.restrict_le_self.absolutelyContinuous : n ≪ m) w hφ hw hwn hdual hcontact h0n
    (K := K) (fun t => ⟨(finiteEntropy_restrict_reference_iff hQ (hs t)).mpr (hcurv t).1, by
      simp only [he]; exact (hcurv t).2⟩)
  simp only [he] at H
  have hi := squareDensity_support_integral (f := fun x => 2*gamma m φ w x) hw.continuous.measurable hQ h0s
  simp only [mul_left_comm (w _) 2] at hi
  have hire : (∫ x, 2*w x*gamma m φ w x ∂n) = ∫ x, 2*w x*gamma m φ w x ∂m := by
    convert hi using 1 <;> congr 1 <;> funext x <;> ring
  simp only [n] at hire
  rwa [hire] at H

variable [SecondCountableTopology X] [ProperSpace X]

theorem RCD.bounded_entropy_subdifferential_oai {m : Measure X} [SigmaFinite m] {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X →ᵇ ℝ) {T : ℝ≥0} (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hdμ : (μ:Measure X) ≤ C • m) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      LipschitzWith (2*R) φ ∧ LipschitzWith (2*R) ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+
        K/2*planEnergy (π:Measure (Curve X)) ≤ ∫ x,2*w x*gamma m φ w x ∂m := by
  obtain ⟨π,hπ,hb,hgeo,hopt,hent,hchord,hcomp⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ ν o R hsμ hsν hC0 hCt hdμ hdν
  obtain ⟨φ,ψ,hφ,hψ,hdual,hcontact⟩ :=
    WeakHessianTransport.bounded_support_kantorovich_potentials
      (isCompact_closedBall o R) (Metric.nonempty_closedBall.mpr R.coe_nonneg)
      (μ:Measure X) (ν:Measure X) (ae_iff.mpr hsμ) (ae_iff.mpr hsν) hopt
      (R := 2*R) (by
        intro x hx y hy
        have H := dist_triangle x o y
        rw [dist_comm o y] at H
        change dist x o ≤ R at hx
        change dist y o ≤ R at hy
        push_cast
        linarith)
  have hc : ∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := by
    apply (ae_map_iff ((continuous_eval_const timeZero).prodMk (continuous_eval_const timeOne)).measurable.aemeasurable ?_).mp hcontact
    exact (isClosed_eq ((hφ.continuous.comp continuous_fst).add (hψ.continuous.comp continuous_snd))
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet
  obtain ⟨h0,h1⟩ := hopt.1.interpolation_endpoints
  refine ⟨π,φ,ψ,hπ,hb,hgeo,hopt,hφ,hψ,hdual,hc,?_⟩
  have H := hπ.entropy_squareRoot_subdifferential_original hfin
    (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hb hgeo w hφ hw hwn hdual hc
    (h0.trans hμ) (K := K) (fun t => ⟨hent t,by simpa only [h0,h1,planEnergy] using hchord t⟩)
  simpa only [h0,h1,planEnergy] using H

end WeakHessian

end
end InlinedFile4

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.bounded_entropy_subdifferential_oai.{u_1} := @OAI.WeakHessian.RCD.bounded_entropy_subdifferential_oai.{u_1}
