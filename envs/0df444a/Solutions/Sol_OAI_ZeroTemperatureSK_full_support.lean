-- Prove2me | solution 1 for OAI.ZeroTemperatureSK.full_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:25.66305+00:00
-- url     : https://prove2.me/submissions/10d5b56d-17dd-4142-9f2b-72428ce4d1e6

import Mathlib
import Definitions.Def_SKFullSupport
import Definitions.Def_OAIQWZT002
import Theorems.Thm_OAI_ZeroTemperatureSK_positive_gap_curvature

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.ExpectedControlPayoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma abs_le_value (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |x| ≤ value W γ t x := by
  let := W.isProbability
  have hmean : (∫ ω, (x + W.B 1 ω - W.B (Real.toNNReal t) ω) ∂W.law) = x := by
    have ha : Integrable (fun ω => x + W.B 1 ω) W.law :=
      (integrable_const x).add (W.brownian.integrable_eval 1)
    rw [integral_sub ha
      (W.brownian.integrable_eval (Real.toNNReal t)),
      integral_add (integrable_const x) (W.brownian.integrable_eval 1)]
    simp [W.brownian.integral_eval]
  calc
    |x| = |∫ ω, (x + W.B 1 ω - W.B (Real.toNNReal t) ω) ∂W.law| := by rw [hmean]
    _ ≤ ∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law :=
      abs_integral_le_integral_abs
    _ = ∫ ω, controlPayoff W γ t x (zeroControl W (Real.toNNReal t)) ω ∂W.law := by
      simp [controlPayoff, zeroControl]
    _ ≤ value W γ t x := expected_controlPayoff_le_value W γ t x ht _

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Semigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

namespace ZeroTemperatureSK.Heat

lemma semigroup_even {f : ℝ → ℝ} (hf : Measurable f) (he : Function.Even f)
    (h : ℝ≥0) : Function.Even (semigroup h f) := by
  intro x
  have hn : HasLaw (fun y : ℝ => -y) (gaussianReal 0 h) (gaussianReal 0 h) := by
    constructor
    · exact measurable_neg.aemeasurable
    · simpa using gaussianReal_map_neg (μ := 0) (v := h)
  have hh := hn.integral_comp (f := fun y => f (-x+y))
    (hf.comp (measurable_const.add measurable_id) |>.aestronglyMeasurable)
  change (∫ y : ℝ, f (-x + -y) ∂gaussianReal 0 h) = semigroup h f (-x) at hh
  rw [← hh]
  unfold semigroup
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← neg_add, he]

lemma logSemigroup_even {f : ℝ → ℝ} (hf : Measurable f) (he : Function.Even f)
    (c : ℝ) (h : ℝ≥0) : Function.Even (logSemigroup c h f) := by
  intro x
  by_cases hc : c = 0
  · simp only [logSemigroup, hc, ↓reduceIte, semigroup_even hf he h x]
  · have hhe : Function.Even (fun z => Real.exp (c*f z)) := by
      intro z
      change Real.exp (c*f (-z)) = Real.exp (c*f z)
      rw [he]
    simp only [logSemigroup, hc, ↓reduceIte]
    exact congrArg (fun v : ℝ => Real.log v/c)
      (semigroup_even (measurable_const.mul hf |>.exp) hhe h x)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.SoftAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma softAbs_even (M : ℝ) : Function.Even (softAbs M) := by
  intro x
  simp [softAbs, Real.cosh_neg]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma semigroup_add {g : ℝ → ℝ} (h k : ℝ≥0) (x : ℝ)
    (hg : Integrable (fun y => g (x+y)) (gaussianReal 0 (h+k))) :
    semigroup (h+k) g x = semigroup h (semigroup k g) x := by
  have he : gaussianReal 0 (h+k) = (gaussianReal 0 h) ∗ (gaussianReal 0 k) := by
    simpa only [zero_add] using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
      (v₁ := h) (v₂ := k)).symm
  rw [he] at hg
  have hh := integral_conv hg
  simpa only [← he, semigroup, add_assoc] using hh

lemma logSemigroup_add {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c : ℝ) (h k : ℝ≥0) (x : ℝ) :
    logSemigroup c (h+k) f x = logSemigroup c h (logSemigroup c k f) x := by
  by_cases hc : c = 0
  · subst c
    have he : logSemigroup 0 k f = semigroup k f := by funext z; simp [logSemigroup]
    simp only [logSemigroup, ↓reduceIte, he]
    exact semigroup_add h k x (integrable_translate_of_lipschitz hf (h+k) x)
  · have he : (fun z => Real.exp (c*logSemigroup c k f z)) =
        semigroup k (fun z => Real.exp (c*f z)) := by
      funext z
      simp only [logSemigroup, hc, ↓reduceIte]
      rw [mul_div_cancel₀ _ hc, Real.exp_log (semigroup_exp_pos hf c k z)]
    rw [logSemigroup, ite_eq_right hc, logSemigroup, ite_eq_right hc, he]
    rw [semigroup_add h k x (integrable_exp_translate_of_lipschitz hf c (h+k) x)]

lemma logSemigroup_terminal_domination {f g : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {c : ℝ} (hc : 0 ≤ c)
    {δ : ℝ} (hδ : ∀ z, f z ≤ g z+δ) (h : ℝ≥0) (x : ℝ) :
    logSemigroup c h f x ≤ logSemigroup c h g x+δ := by
  by_cases hc0 : c = 0
  · subst c
    simp only [logSemigroup, ↓reduceIte]
    have hh := integral_mono (integrable_translate_of_lipschitz hf h x)
      ((integrable_translate_of_lipschitz hg h x).add (integrable_const δ)) (fun y => hδ (x+y))
    change (∫ y, f (x+y) ∂gaussianReal 0 h) ≤ (∫ y, g (x+y)+δ ∂gaussianReal 0 h) at hh
    rw [integral_add (integrable_translate_of_lipschitz hg h x) (integrable_const δ)] at hh
    simpa [semigroup, integral_const, Measure.real] using hh
  · have hcp := lt_of_le_of_ne hc (Ne.symm hc0)
    have hE : semigroup h (fun z => Real.exp (c*f z)) x ≤
        Real.exp (c*δ)*semigroup h (fun z => Real.exp (c*g z)) x := by
      unfold semigroup
      rw [← integral_const_mul]
      apply integral_mono (integrable_exp_translate_of_lipschitz hf c h x)
        ((integrable_exp_translate_of_lipschitz hg c h x).const_mul _)
      intro y
      change Real.exp (c*f (x+y)) ≤ Real.exp (c*δ)*Real.exp (c*g (x+y))
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hδ (x+y)]
    have hh := Real.log_le_log (semigroup_exp_pos hf c h x) hE
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (semigroup_exp_pos hg c h x)), Real.log_exp] at hh
    simp only [logSemigroup, hc0, ↓reduceIte]
    apply (div_le_iff₀ hcp).mpr
    field_simp
    nlinarith

lemma logSemigroup_terminal_stability {f g : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {c : ℝ} (hc : 0 ≤ c)
    {δ : ℝ} (hδ : ∀ z, |f z-g z| ≤ δ) (h : ℝ≥0) (x : ℝ) :
    |logSemigroup c h f x-logSemigroup c h g x| ≤ δ := by
  have h₁ := logSemigroup_terminal_domination hf hg hc (δ := δ)
    (fun z => by linarith [(abs_le.mp (hδ z)).2]) h x
  have h₂ := logSemigroup_terminal_domination hg hf hc (δ := δ)
    (fun z => by linarith [(abs_le.mp (hδ z)).1]) h x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.FamilyReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma scaled_composition_jet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) (n : ℕ) (x : ℝ) :
    _root_.iteratedDeriv n (fun y => f (a*y)) x = a^n*_root_.iteratedDeriv n f (a*x) := by
  exact congrFun (iteratedDeriv_comp_const_mul
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) a) x

lemma BoundedSmoothFamily.reparam {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    {A C : ℝ → ℝ} (hA : Measurable A) (hC : Measurable C) (hb : ∀ t, |C t| ≤ 1) :
    BoundedSmoothFamily (fun t x => F (A t) (C t*x)) := by
  have hbound (n : ℕ) : ∃ K : ℝ≥0, ∀ t x,
      |_root_.iteratedDeriv n (fun y => F (A t) (C t*y)) x| ≤ K := by
    obtain ⟨K,hK⟩ := hF.bounds n
    refine ⟨K,fun t x => ?_⟩
    rw [scaled_composition_jet (hF.regular (A t)).smooth,abs_mul,abs_pow]
    calc
      |C t|^n*|_root_.iteratedDeriv n (F (A t)) (C t*x)| ≤ 1*(K:ℝ) :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) (hb t)) (hK _ _) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  refine ⟨hF.measurable.comp ((hA.comp measurable_fst).prodMk
    ((hC.comp measurable_fst).mul measurable_snd)),?_,hbound⟩
  intro t
  refine ⟨(hF.regular (A t)).smooth.comp (contDiff_const.mul contDiff_id),?_⟩
  intro n
  obtain ⟨K,hK⟩ := hbound n
  exact ⟨K,hK t⟩

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.GaussianFlowRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.continuousOn_iteratedDeriv {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hF : BoundedSmoothFamily F)
    (hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ)) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => _root_.iteratedDeriv n (F p.1) p.2) (S ×ˢ univ) := by
  induction n with
  | zero => exact hc
  | succ n hn =>
    obtain ⟨C,hC⟩ := (hF.iteratedDeriv n).deriv.deriv.bound
    simpa only [iteratedDeriv_succ] using continuousOn_deriv_family hn
      (fun t _ => ((hF.iteratedDeriv n).regular t).smooth.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) C.coe_nonneg
      (fun t _ x => hC t x)

lemma varianceGradient_family {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (fun t => deriv (varianceLogHeat c t f)) := by
  have hm : Measurable (fun p : ℝ × ℝ => varianceLogHeat c p.1 f p.2) := by
    have hh := (measurable_backward hf.smooth.continuous.measurable c 0).comp
      (measurable_fst.neg.prodMk measurable_snd)
    simpa only [Function.comp_def,Pi.neg_apply,backward,zero_sub,neg_neg] using hh
  refine ⟨measurable_spatial_deriv hm (fun t =>
    (regularDatum_varianceLogHeat hf hLip hc t).smooth.differentiable (by simp)),
    fun t => (regularDatum_varianceLogHeat hf hLip hc t).deriv_bounded,?_⟩
  intro n
  simpa only [iteratedDeriv_succ'] using uniform_varianceLogHeat_derivative_bounds hf hLip hc n

lemma varianceGradient_continuousOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL⟩ := varianceTilted_joint_bound hf hLip hf.deriv_bounded hc
  apply continuousOn_of_joint_bound (F := fun t => deriv (varianceLogHeat c t f)) (L := L)
  intro t ht s hs x y
  rw [deriv_varianceLogHeat_tilted hf hLip hc,deriv_varianceLogHeat_tilted hf hLip hc]
  exact hL t ht.1 s hs.1 x y

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.continuous_iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => _root_.iteratedDeriv n (F p.1) p.2) := by
  exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using
    hF.continuousOn_iteratedDeriv (S := univ) hc.continuousOn n)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.AffineEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma tiltedMean_nonneg {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hg : ∀ x, 0 ≤ g x) (c : ℝ) (h : ℝ≥0) (x : ℝ) : 0 ≤ tiltedMean c h f g x := by
  apply div_nonneg _ (semigroup_exp_pos hf c h x).le
  exact integral_nonneg (fun y => mul_nonneg (hg _) (Real.exp_nonneg _))

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Control.ControlPayoffConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma controlPayoff_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    ConvexOn ℝ Set.univ (fun x => controlPayoff W γ t x α ω) := by
  have h := ((convexOn_norm (E := ℝ) (s := Set.univ) convex_univ).translate_left
    (W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s-t)) ω)).add_const
    (-(1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s-t)) ω)^2)
  simpa only [Set.preimage_univ, Function.comp_def, Pi.add_def, Pi.add_apply, Real.norm_eq_abs, controlPayoff,
    sub_eq_add_neg, neg_mul, add_assoc] using h

lemma expected_controlPayoff_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    ConvexOn ℝ Set.univ (fun x => ∫ ω, controlPayoff W γ t x α ω ∂W.law) := by
  exact integral_convexOn_of_integrand_ae convex_univ
    (Filter.Eventually.of_forall (controlPayoff_convex W γ t α))
    (fun x _ => controlPayoff_integrable W γ t x ht α)

theorem value_convex (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) : ConvexOn ℝ Set.univ (value W γ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  change sSup (Set.range (fun α : Control W (Real.toNNReal t) =>
    ∫ ω, controlPayoff W γ t (a*x+b*y) α ω ∂W.law)) ≤ _
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    _ ≤ a * (∫ ω, controlPayoff W γ t x α ω ∂W.law) +
        b * (∫ ω, controlPayoff W γ t y α ω ∂W.law) := by
      simpa only [smul_eq_mul] using
        (expected_controlPayoff_convex W γ t ht α).2 hx hy ha hb hab
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (expected_controlPayoff_le_value W γ t x ht α) ha)
      (mul_le_mul_of_nonneg_left (expected_controlPayoff_le_value W γ t y ht α) hb)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma cascade_even {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (he : Function.Even f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Function.Even (cascade c h f N i) := by
  induction N generalizing i with
  | zero => exact he
  | succ N ih =>
    exact logSemigroup_even (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable
      (ih (i+1)) (c i) h

lemma finiteValue_even {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (he : Function.Even f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    Function.Even (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact he
  | succ N ih =>
    by_cases ht : t ≤ h
    · rw [finiteValue_head f c h N i ht]
      have hm := (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable
      have heq : backward (c i) h (cascade c h f N (i+1)) t =
          logSemigroup (c i) (Real.toNNReal (h-t)) (cascade c h f N (i+1)) :=
        funext (varianceLogHeat_eq_logSemigroup_toNNReal hm (c i) (h-t))
      rw [heq]
      exact logSemigroup_even hm (cascade_even hf hLip he c h N (i+1)) _ _
    · rw [finiteValue_tail f c h N i (lt_of_not_ge ht)]
      exact ih (i+1) (t-h)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem value_even (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Function.Even (value W γ t) := by
  intro x
  have h₁ := (approxValue_uniform_spatial W γ ht0 ht1).tendsto_at (-x)
  have h₂ := (approxValue_uniform_spatial W γ ht0 ht1).tendsto_at x
  apply tendsto_nhds_unique h₁
  exact h₂.congr (fun n => (finiteValue_even (regularDatum_softAbs (by positivity))
    (softAbs_lipschitz (by positivity)) (softAbs_even _) _ _ _ _ t x).symm)

lemma gradient_odd (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : Function.Odd (gradient W γ t) := by
  intro x
  have hf := (value_contDiff W γ ht0 ht1).differentiable (by simp)
  have hcomp := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have he : (fun y => value W γ t (-y)) = value W γ t := funext (value_even W γ ht0 ht1.le)
  change HasDerivAt (fun y => value W γ t (-y)) _ x at hcomp
  rw [he] at hcomp
  have hd := hcomp.deriv
  change deriv (value W γ t) x = deriv (value W γ t) (-x)*(-1) at hd
  unfold gradient
  linarith

lemma gradient_zero (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : gradient W γ t 0 = 0 := by
  have hh := gradient_odd W γ ht0 ht1 0
  simp only [neg_zero] at hh
  linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.PicardDiffusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_time_measurable (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) (ω : Ω) : Measurable (fun t : ℝ => α (Real.toNNReal t) ω) :=
  ((progressive_joint_measurable ℱ ha).comp
    (measurable_id.prodMk measurable_const)).comp measurable_real_toNNReal

lemma progressive_bounded_integrable (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun t => α (Real.toNNReal t) ω) volume a b := by
  apply (intervalIntegrable_const (c := D)).mono_fun
  · exact (progressive_time_measurable ℱ ha ω).aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using (hb (Real.toNNReal t) ω).trans (le_abs_self D)

lemma timePrimitive_continuous (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (ω : Ω) :
    Continuous (fun t => timePrimitive α t ω) :=
  (intervalIntegral.continuous_primitive (progressive_bounded_integrable ℱ ha hb ω) 0).comp
    continuous_subtype_val

lemma timePrimitive_progressive (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) :
    IsProgressive ℱ (timePrimitive α) := by
  have hm : StronglyAdapted ℱ (timePrimitive α) := by
    intro t
    have hh := progressive_integral_measurable ℱ ha t (w := fun _ => 1) measurable_const
    change StronglyMeasurable[ℱ t] (fun ω => ∫ s in (0:ℝ)..(t:ℝ), α (Real.toNNReal s) ω)
    simpa only [one_mul] using hh.stronglyMeasurable
  exact (hm.isStronglyProgressive_of_continuous (timePrimitive_continuous ℱ ha hb)).isProgressive

lemma timePrimitive_bound (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (t : ℝ≥0) (ω : Ω) :
    |timePrimitive α t ω| ≤ D*(t:ℝ) := by
  calc
    |timePrimitive α t ω| ≤ ∫ s in (0:ℝ)..(t:ℝ), |α (Real.toNNReal s) ω| :=
      intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg
    _ ≤ ∫ _s in (0:ℝ)..(t:ℝ), D :=
      intervalIntegral.integral_mono t.coe_nonneg
        (progressive_bounded_integrable ℱ ha hb ω 0 t).abs intervalIntegrable_const
        (fun _ => hb _ _)
    _ = D*(t:ℝ) := by simp [mul_comm]

namespace BoundedLipschitzDrift

variable (b : BoundedLipschitzDrift)

lemma action_progressive (ℱ : Filtration ℝ≥0 mΩ) {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y) : IsProgressive ℱ (b.action B Y) := by
  intro t
  exact b.measurable.comp ((measurable_subtype_coe.comp (measurable_subtype_coe.comp
    measurable_fst)).prodMk ((hB t).add (hY t)))

omit mΩ in
lemma action_bound (B Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    |b.action B Y t ω| ≤ b.bound := b.bounded _ _

lemma correctionIter_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) : IsProgressive ℱ (b.correctionIter B n) := by
  induction n with
  | zero => exact isProgressive_const ℱ 0
  | succ n hn => exact timePrimitive_progressive ℱ (b.action_progressive ℱ hB hn) (b.action_bound _ _)

lemma correctionIter_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |b.correctionIter B n t ω| ≤ (b.bound:ℝ)*(t:ℝ) := by
  cases n with
  | zero => simpa only [correctionIter,abs_zero] using mul_nonneg b.bound.coe_nonneg t.coe_nonneg
  | succ n =>
    exact timePrimitive_bound ℱ
      (b.action_progressive ℱ hB (b.correctionIter_progressive ℱ hB n)) (b.action_bound _ _) t ω

lemma rate_pos : 0 < b.rate := by unfold rate; positivity
lemma one_le_rate : 1 ≤ b.rate := by unfold rate; linarith [b.lip.coe_nonneg]

lemma integral_exp_rate (t : ℝ≥0) :
    (∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s))*b.rate = Real.exp (b.rate*t)-1 := by
  have hd (s : ℝ) : HasDerivAt (fun r => Real.exp (b.rate*r))
      (Real.exp (b.rate*s)*b.rate) s := by
    convert ((hasDerivAt_id s).const_mul b.rate).exp using 1 <;> simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const).intervalIntegrable _ _)
    (a := (0:ℝ)) (b := (t:ℝ))
  simpa only [intervalIntegral.integral_mul_const,mul_zero,Real.exp_zero] using hh

lemma integral_exp_contraction {A : ℝ} (hA : 0 ≤ A) (t : ℝ≥0) :
    (∫ s in (0:ℝ)..(t:ℝ), (b.lip:ℝ)*A*Real.exp (b.rate*s)) ≤
      A/2*Real.exp (b.rate*t) := by
  rw [intervalIntegral.integral_const_mul]
  have hi : 0 ≤ ∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s) :=
    intervalIntegral.integral_nonneg t.coe_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hl : (b.lip:ℝ) ≤ b.rate/2 := by unfold rate; linarith
  calc
    _ ≤ (b.rate/2)*A*(∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hA) hi
    _ = A/2*(Real.exp (b.rate*t)-1) := by rw [← b.integral_exp_rate t]; ring
    _ ≤ A/2*Real.exp (b.rate*t) := by nlinarith

lemma timePrimitive_action_sub_estimate (ℱ : Filtration ℝ≥0 mΩ)
    {B Y Z : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y)
    (hZ : IsProgressive ℱ Z) {A : ℝ} (hA : 0 ≤ A) (t : ℝ≥0) (ω : Ω)
    (he : ∀ s ≤ t, |Y s ω-Z s ω| ≤ A*Real.exp (b.rate*s)) :
    |timePrimitive (b.action B Y) t ω-timePrimitive (b.action B Z) t ω| ≤
      A/2*Real.exp (b.rate*t) := by
  have hiY := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hY) (b.action_bound B Y) ω 0 t
  have hiZ := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hZ) (b.action_bound B Z) ω 0 t
  rw [timePrimitive,timePrimitive,← intervalIntegral.integral_sub hiY hiZ]
  apply le_trans _ (b.integral_exp_contraction hA t)
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  filter_upwards [] with s hs
  have hst : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hh := he _ hst
  have hl := (b.lipschitz (Real.toNNReal s)).dist_le_mul
    (B (Real.toNNReal s) ω+Y (Real.toNNReal s) ω)
    (B (Real.toNNReal s) ω+Z (Real.toNNReal s) ω)
  simp only [Real.dist_eq,add_sub_add_left_eq_sub] at hl
  simp only [Real.coe_toNNReal _ hs.1.le] at hh
  change |b.action B Y (Real.toNNReal s) ω-b.action B Z (Real.toNNReal s) ω| ≤ _
  exact hl.trans (by simpa only [mul_assoc,Pi.mul_apply,Function.comp_apply,id_eq] using mul_le_mul_of_nonneg_left hh b.lip.coe_nonneg)

lemma correctionIter_diff_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |b.correctionIter B (n+1) t ω-b.correctionIter B n t ω| ≤
      (b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t) := by
  induction n generalizing t with
  | zero =>
    simp only [correctionIter,_root_.sub_zero,pow_zero,mul_one]
    apply (timePrimitive_bound ℱ (b.action_progressive ℱ hB (isProgressive_const ℱ 0))
      (b.action_bound _ _) t ω).trans
    apply mul_le_mul_of_nonneg_left _ b.bound.coe_nonneg
    have ht : (t:ℝ) ≤ b.rate*t := by nlinarith [b.one_le_rate,t.coe_nonneg]
    linarith [Real.add_one_le_exp (b.rate*t)]
  | succ n hn =>
    have hh := b.timePrimitive_action_sub_estimate ℱ hB
      (b.correctionIter_progressive ℱ hB (n+1)) (b.correctionIter_progressive ℱ hB n)
      (show 0 ≤ (b.bound:ℝ)*(1/2:ℝ)^n by positivity) t ω (fun s _ => hn s)
    convert hh using 1 <;> simp only [correctionIter,pow_succ]
    ring

lemma correctionIter_tendsto (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => b.correctionIter B n t ω) atTop (𝓝 (b.correction B t ω)) := by
  apply CauchySeq.tendsto_limUnder
  apply cauchySeq_of_le_geometric (1/2:ℝ) ((b.bound:ℝ)*Real.exp (b.rate*t)) (by norm_num)
  intro n
  rw [Real.dist_eq,abs_sub_comm]
  convert b.correctionIter_diff_bound ℱ hB n t ω using 1 <;> try rfl
  ring

lemma correction_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) : IsProgressive ℱ (b.correction B) := by
  intro t
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ t)]
      (fun p : Iic t × Ω => b.correctionIter B n p.1 p.2) :=
    (b.correctionIter_progressive ℱ hB n t).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ t
  exact (StronglyMeasurable.limUnder hm).measurable

lemma correction_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    |b.correction B t ω| ≤ (b.bound:ℝ)*(t:ℝ) :=
  le_of_tendsto (b.correctionIter_tendsto ℱ hB t ω).abs
    (Eventually.of_forall (fun n => b.correctionIter_bound ℱ hB n t ω))

lemma correction_eq_integral (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    b.correction B t ω = timePrimitive (b.action B (b.correction B)) t ω := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun s : ℝ => b.action B (b.correctionIter B n) (Real.toNNReal s) ω)
      (volume.restrict (Ioc 0 (t:ℝ))) :=
    (progressive_time_measurable ℱ (b.action_progressive ℱ hB
      (b.correctionIter_progressive ℱ hB n)) ω).aestronglyMeasurable
  have hd (n : ℕ) : ∀ᵐ s ∂volume.restrict (Ioc 0 (t:ℝ)),
      ‖b.action B (b.correctionIter B n) (Real.toNNReal s) ω‖ ≤ (b.bound:ℝ) :=
    Eventually.of_forall (fun s => b.action_bound _ _ _ _)
  have hl : ∀ᵐ s ∂volume.restrict (Ioc 0 (t:ℝ)), Tendsto
      (fun n => b.action B (b.correctionIter B n) (Real.toNNReal s) ω) atTop
      (𝓝 (b.action B (b.correction B) (Real.toNNReal s) ω)) := by
    filter_upwards [] with s
    exact ((b.lipschitz (Real.toNNReal s)).continuous.tendsto _).comp
      (tendsto_const_nhds.add (b.correctionIter_tendsto ℱ hB (Real.toNNReal s) ω))
  have hi : Integrable (fun _ : ℝ => (b.bound:ℝ)) (volume.restrict (Ioc 0 (t:ℝ))) :=
    (intervalIntegrable_const (c := (b.bound:ℝ))).1
  have hh := tendsto_integral_of_dominated_convergence (fun _ => (b.bound:ℝ)) hm hi hd hl
  have hh' : Tendsto (fun n => b.correctionIter B (n+1) t ω) atTop
      (𝓝 (timePrimitive (b.action B (b.correction B)) t ω)) := by
    simpa only [correctionIter,timePrimitive,intervalIntegral.integral_of_le t.coe_nonneg] using hh
  exact tendsto_nhds_unique ((b.correctionIter_tendsto ℱ hB t ω).comp (tendsto_add_atTop_nat 1)) hh'

lemma correction_continuous (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (ω : Ω) : Continuous (fun t => b.correction B t ω) := by
  have he : (fun t => b.correction B t ω) =
      (fun t => timePrimitive (b.action B (b.correction B)) t ω) :=
    funext (fun t => b.correction_eq_integral ℱ hB t ω)
  rw [he]
  exact timePrimitive_continuous ℱ (b.action_progressive ℱ hB (b.correction_progressive ℱ hB))
    (b.action_bound _ _) ω

lemma solution_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) : IsProgressive ℱ (b.solution B) := hB.add (b.correction_progressive ℱ hB)

lemma solution_eq (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    b.solution B t ω = B t ω+∫ s in (0:ℝ)..(t:ℝ),
      b.f (Real.toNNReal s) (b.solution B (Real.toNNReal s) ω) := by
  change B t ω+b.correction B t ω = B t ω+_
  rw [b.correction_eq_integral ℱ hB t ω]
  rfl

lemma solution_continuous (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) {ω : Ω} (hc : Continuous (fun t => B t ω)) :
    Continuous (fun t => b.solution B t ω) := hc.add (b.correction_continuous ℱ hB ω)

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.ProgressiveBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma leftMeshTime_le (n : ℕ) (t : ℝ≥0) : leftMeshTime n t ≤ t := by
  apply NNReal.coe_le_coe.mp
  simp only [leftMeshTime,NNReal.coe_div,NNReal.coe_natCast]
  apply (div_le_iff₀ (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)).mpr
  have hh := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (α := ℝ) (n+1)) t.coe_nonneg)
  nlinarith

lemma leftMeshTime_gt (n : ℕ) (t : ℝ≥0) : (t:ℝ)-1/((n+1:ℕ):ℝ) < leftMeshTime n t := by
  simp only [leftMeshTime,NNReal.coe_div,NNReal.coe_natCast]
  have hh := Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*(t:ℝ))
  apply (lt_div_iff₀ (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)).mpr
  have he : ((t:ℝ)-1/((n+1:ℕ):ℝ))*((n+1:ℕ):ℝ) = ((n+1:ℕ):ℝ)*(t:ℝ)-1 := by
    field_simp
  rw [he]
  linarith

lemma leftMeshTime_tendsto (t : ℝ≥0) : Tendsto (fun n => leftMeshTime n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  have hl : Tendsto (fun n : ℕ => (t:ℝ)-1/((n+1:ℕ):ℝ)) atTop (𝓝 (t:ℝ)) := by
    simpa only [sub_zero,Nat.cast_add,Nat.cast_one] using
      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := (t:ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (leftMeshTime_gt n t).le) (fun n => leftMeshTime_le n t)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma leftMesh_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : Adapted ℱ B) (n : ℕ) : IsProgressive ℱ (fun t ξ => B (leftMeshTime n t) ξ) := by
  intro s
  have hm (k : ℕ) : Measurable[ℱ s] (B (min ((k:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s)) :=
    (hB _).mono (ℱ.mono (min_le_right _ _)) le_rfl
  let : MeasurableSpace Ω := ℱ s
  have hprod : Measurable[(inferInstance : MeasurableSpace ℕ).prod (ℱ s)]
      (fun p : ℕ × Ω => B (min ((p.1:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s) p.2) := by
    let : MeasurableSpace Ω := ℱ s
    exact measurable_from_prod_countable_right hm
  have ht : Measurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => ((p.1:ℝ≥0):ℝ)) := by fun_prop
  have hi : Measurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => ⌊((n+1:ℕ):ℝ)*((p.1:ℝ≥0):ℝ)⌋₊) :=
    (measurable_const.mul ht).nat_floor
  have hh := hprod.comp (hi.prodMk measurable_snd)
  have he : (fun p : Set.Iic s × Ω => B (leftMeshTime n p.1) p.2) =
      (fun p : ℕ × Ω => B (min ((p.1:ℝ≥0)/((n+1:ℕ):ℝ≥0)) s) p.2) ∘
        (fun p : Set.Iic s × Ω => (⌊((n+1:ℕ):ℝ)*((p.1:ℝ≥0):ℝ)⌋₊,p.2)) := by
    funext p
    have hle := (leftMeshTime_le n (p.1:ℝ≥0)).trans p.1.property
    dsimp only [leftMeshTime] at hle
    simp only [Function.comp_def,leftMeshTime,min_eq_left hle]
  rw [he]
  exact hh

lemma BrownianSystem.progressiveVersion_progressive (W : BrownianSystem Ω) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      W.progressiveVersion := by
  intro s
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hn : Adapted ℱ W.B := fun t =>
    (Filtration.stronglyAdapted_natural (fun t => (W.measurable t).stronglyMeasurable) t).measurable
  let B : ℝ≥0 → Ω → ℝ := W.B
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ s)]
      (fun p : Set.Iic s × Ω => B (leftMeshTime n p.1) p.2) :=
    (leftMesh_progressive ℱ hn n s).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ s
  exact (StronglyMeasurable.limUnder hm).measurable

lemma BrownianSystem.progressiveVersion_eq (W : BrownianSystem Ω) {ξ : Ω}
    (hc : Continuous (fun t => W.B t ξ)) (t : ℝ≥0) : W.progressiveVersion t ξ = W.B t ξ :=
  ((hc.tendsto t).comp (leftMeshTime_tendsto t)).limUnder_eq

lemma BrownianSystem.progressiveVersion_indistinguishable (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, ∀ t, W.progressiveVersion t ξ = W.B t ξ := by
  filter_upwards [W.brownian.cont] with ξ hξ
  exact W.progressiveVersion_eq hξ

lemma BrownianSystem.driver_progressive (W : BrownianSystem Ω) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)) W.driver := by
  intro s
  have hm := W.progressiveVersion_progressive.adapted 0
  have hm' := hm.mono ((Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)).mono
    (show (0:ℝ≥0) ≤ s by positivity)) le_rfl
  exact (W.progressiveVersion_progressive s).sub (hm'.comp measurable_snd)

lemma BrownianSystem.driver_zero (W : BrownianSystem Ω) (ξ : Ω) : W.driver 0 ξ = 0 := sub_self _

lemma BrownianSystem.driver_indistinguishable (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, ∀ t, W.driver t ξ = W.B t ξ := by
  filter_upwards [W.progressiveVersion_indistinguishable,W.brownian.eval_zero_ae_eq_zero] with ξ hh h₀ t
  simp only [BrownianSystem.driver,hh,h₀,sub_zero]

lemma BrownianSystem.driver_continuous (W : BrownianSystem Ω) :
    ∀ᵐ ξ ∂W.law, Continuous (fun t => W.driver t ξ) := by
  filter_upwards [W.driver_indistinguishable,W.brownian.cont] with ξ hh hc
  simpa only [hh] using hc

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.TiltedEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceTilted_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) : BoundedSmoothFamily (fun t => varianceTilted c t f g) := by
  have he (t : ℝ) : varianceTilted c t f g=tiltedMean c (Real.toNNReal t) f g :=
    funext (varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable hg.smooth.continuous.measurable c t)
  refine ⟨?_,fun t => by rw [he];exact boundedSmooth_tiltedMean hf hLip hg hc _,?_⟩
  · exact (measurable_varianceHeat_family (F := fun _ y => g y*Real.exp (c*f y))
      (hg.smooth.continuous.measurable.comp measurable_snd |>.mul
        ((measurable_const.mul (hf.smooth.continuous.measurable.comp measurable_snd)).exp)) measurable_id).div
      (measurable_varianceHeat_family (F := fun _ y => Real.exp (c*f y))
        ((measurable_const.mul (hf.smooth.continuous.measurable.comp measurable_snd)).exp) measurable_id)
  · intro n
    obtain ⟨C,hC⟩ := uniform_tiltedMean_bounds hf hLip hg hc n
    exact ⟨C,fun t x => by rw [he];exact hC _ x⟩

lemma second_deriv_mul {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (x : ℝ) :
    deriv (deriv (fun y => F y*G y)) x =
      deriv (deriv F) x*G x+2*deriv F x*deriv G x+F x*deriv (deriv G) x := by
  have he : deriv (fun y => F y*G y)=fun y => deriv F y*G y+F y*deriv G y := by
    funext y
    exact (((hF.differentiable (by norm_num)) y).hasDerivAt.mul
      ((hG.differentiable (by norm_num)) y).hasDerivAt).deriv
  rw [he]
  convert (((((show ContDiff ℝ 1 (deriv F) from hF.deriv').differentiable (by norm_num)) x).hasDerivAt.mul
    ((hG.differentiable (by norm_num)) x).hasDerivAt).add
    (((hF.differentiable (by norm_num)) x).hasDerivAt.mul
    (((show ContDiff ℝ 1 (deriv G) from hG.deriv').differentiable (by norm_num)) x).hasDerivAt)).deriv using 1 <;> try rfl
  ring

lemma quotient_heat_equation {N D : ℝ → ℝ → ℝ} {t : ℝ} {S : Set ℝ}
    (hN : ContDiff ℝ 2 (N t)) (hD : ContDiff ℝ 2 (D t))
    (hne : ∀ x, D t x ≠ 0)
    (hNt : ∀ x, HasDerivWithinAt (fun u => N u x) ((1/2:ℝ)*deriv (deriv (N t)) x) S t)
    (hDt : ∀ x, HasDerivWithinAt (fun u => D u x) ((1/2:ℝ)*deriv (deriv (D t)) x) S t) (x : ℝ) :
    HasDerivWithinAt (fun u => N u x/D u x)
      ((1/2:ℝ)*deriv (deriv (fun y => N t y/D t y)) x+
        (deriv (D t) x/D t x)*deriv (fun y => N t y/D t y) x) S t := by
  let F := fun y => N t y/D t y
  have hF : ContDiff ℝ 2 F := hN.div hD hne
  have he : N t=fun y => F y*D t y := by funext y;dsimp [F];field_simp [hne y]
  have hxx : deriv (deriv (N t)) x=deriv (deriv F) x*D t x+
      2*deriv F x*deriv (D t) x+F x*deriv (deriv (D t)) x := by
    calc
      _ = deriv (deriv (fun y => F y*D t y)) x := congrArg (fun f => deriv (deriv f) x) he
      _ = _ := second_deriv_mul hF hD x
  convert (hNt x).div (hDt x) (hne x) using 1 <;> try rfl
  rw [hxx]
  dsimp only [F]
  field_simp [hne x]
  ring

lemma varianceTilted_equation {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun u => varianceTilted c u f g x)
      ((1/2:ℝ)*deriv (deriv (varianceTilted c t f g)) x+
        c*deriv (varianceLogHeat c t f) x*deriv (varianceTilted c t f g) x) (Ici 0) t := by
  let N := fun u => varianceHeat u (fun y => g y*Real.exp (c*f y))
  let D := fun u => varianceHeat u (fun y => Real.exp (c*f y))
  have hD (u : ℝ) : ContDiff ℝ ∞ (D u) := by
    have he : D u=semigroup (Real.toNNReal u) (fun y => Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal ((measurable_const.mul hf.smooth.continuous.measurable).exp) u)
    rw [he]
    exact contDiff_semigroup_exp hf hLip hc _
  have hN (u : ℝ) : ContDiff ℝ ∞ (N u) := by
    have he : N u=semigroup (Real.toNNReal u) (fun y => g y*Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal (hg.smooth.continuous.measurable.mul
        ((measurable_const.mul hf.smooth.continuous.measurable).exp)) u)
    rw [he]
    exact contDiff_semigroup_weight_exp hf hLip hg hc _
  have hNt (y : ℝ) : HasDerivWithinAt (fun u => N u y) ((1/2:ℝ)*deriv (deriv (N t)) y) (Ici 0) t :=
    varianceHeat_equation ((hg.smooth.mul (contDiff_const.mul hf.smooth).exp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (by simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0)
      (by simpa only [iteratedDeriv_one] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 1)
      (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 2) ht y
  have hDt (y : ℝ) : HasDerivWithinAt (fun u => D u y) ((1/2:ℝ)*deriv (deriv (D t)) y) (Ici 0) t := by
    convert varianceHeat_equation ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_exp hLip c)
      (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
      (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2) ht y using 1 <;> try rfl
  have hratio : deriv (D t) x/D t x=c*deriv (varianceLogHeat c t f) x := by
    rw [deriv_varianceLogHeat_tilted hf hLip hc]
    have hd := hasDerivAt_semigroup_exp (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hLip hc (Real.toNNReal t) x
    have he : D t=semigroup (Real.toNNReal t) (fun y => Real.exp (c*f y)) :=
      funext (varianceHeat_eq_semigroup_toNNReal ((measurable_const.mul hf.smooth.continuous.measurable).exp) t)
    rw [he,hd.deriv,varianceTilted_eq_tiltedMean hf.smooth.continuous.measurable hf.deriv_bounded.smooth.continuous.measurable]
    simp only [tiltedMean,semigroup]
    rw [← mul_div_assoc,← integral_const_mul]
    apply congrArg (fun z : ℝ => z / ∫ y, Real.exp (c*f (x+y)) ∂gaussianReal 0 (Real.toNNReal t))
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hh := quotient_heat_equation ((hN t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((hD t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun y => ne_of_gt (varianceHeat_exp_pos hLip c t y)) hNt hDt x
  rw [hratio] at hh
  exact hh

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.TiltedBackward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma varianceTilted_time_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) (c x : ℝ) :
    Continuous (fun t => varianceTilted c t f g x) := by
  have hNc : Continuous (fun y => g y*Real.exp (c*f y)) :=
    hg.smooth.continuous.mul (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
  have hNb : ExponentialBound (fun y => g y*Real.exp (c*f y)) := by
    simpa only [iteratedDeriv_zero] using exponentialBound_weightExp_iteratedDeriv hf hLip hg c 0
  exact (continuous_varianceHeat hNc hNb x).div
    (continuous_varianceHeat (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
      (exponentialBound_exp hLip c) x)
    (fun t => ne_of_gt (varianceHeat_exp_pos hLip c t x))

lemma varianceTilted_joint_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => varianceTilted c p.1 f g p.2) := by
  obtain ⟨L,hL⟩ := varianceTilted_space_lipschitz hf hLip hg hc
  apply continuous_iff_continuousAt.mpr
  intro p
  have hlim : Tendsto (fun q : ℝ × ℝ => (L:ℝ)*|q.2-p.2|+
      |varianceTilted c q.1 f g p.2-varianceTilted c p.1 f g p.2|) (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : ℝ × ℝ => (L:ℝ)*|q.2-p.2|+
        |varianceTilted c q.1 f g p.2-varianceTilted c p.1 f g p.2|) := by
      exact (continuous_const.mul (continuous_snd.sub continuous_const).abs).add
        (((varianceTilted_time_continuous hf hLip hg c p.2).comp continuous_fst).sub continuous_const).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hh.continuousAt.tendsto (x := p)
  change Tendsto (fun q : ℝ × ℝ => varianceTilted c q.1 f g q.2) (𝓝 p)
    (𝓝 (varianceTilted c p.1 f g p.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with q hq
  have hb := (hL q.1).dist_le_mul q.2 p.2
  have htri := dist_triangle (varianceTilted c q.1 f g q.2) (varianceTilted c q.1 f g p.2)
    (varianceTilted c p.1 f g p.2)
  simp only [Real.dist_eq] at hb htri ⊢
  exact (htri.trans (add_le_add hb le_rfl)).trans_lt hq

lemma tiltedRate_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (tiltedRate c f g) := by
  have hU := varianceTilted_family hf hLip hg hc
  exact (hU.deriv.deriv.const_mul (1/2:ℝ)).add (((varianceGradient_family hf hLip hc).const_mul c).mul hU.deriv)

lemma tiltedRate_continuousOn {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => tiltedRate c f g p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  have hU := varianceTilted_family hf hLip hg hc
  have hUc := varianceTilted_joint_continuous hf hLip hg hc
  have hUx := hU.continuous_iteratedDeriv hUc 1
  have hUxx := hU.continuous_iteratedDeriv hUc 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hUx hUxx
  exact (continuous_const.mul hUxx).continuousOn.add
    ((continuousOn_const.mul (varianceGradient_continuousOn hf hLip hc T)).mul hUx.continuousOn)

lemma tiltedBackward_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    BoundedSmoothFamily (tiltedBackward c T f g) := by
  unfold tiltedBackward
  simpa only [one_mul] using (varianceTilted_family hf hLip hg hc).reparam
    (A := fun t => T-t) (C := fun _ => 1) (measurable_const.sub measurable_id) measurable_const (fun _ => by norm_num)

lemma tiltedBackwardRate_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    BoundedSmoothFamily (tiltedBackwardRate c T f g) := by
  unfold tiltedBackwardRate
  simpa only [one_mul,neg_one_mul] using ((tiltedRate_family hf hLip hg hc).reparam
    (A := fun t => T-t) (C := fun _ => 1) (measurable_const.sub measurable_id) measurable_const
    (fun _ => by norm_num)).const_mul (-1)

lemma tiltedBackward_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    Continuous (fun p : ℝ × ℝ => tiltedBackward c T f g p.1 p.2) :=
  (varianceTilted_joint_continuous hf hLip hg hc).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)

lemma tiltedBackwardRate_continuousOn {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => tiltedBackwardRate c T f g p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  change ContinuousOn (fun p : ℝ × ℝ => -tiltedRate c f g (T-p.1) p.2) _
  exact (tiltedRate_continuousOn hf hLip hg hc T |>.neg).comp
    (f := fun p : ℝ × ℝ => (T-p.1,p.2))
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    (fun p hp => ⟨⟨sub_nonneg.mpr hp.1.2,sub_le_self _ hp.1.1⟩,mem_univ _⟩)

lemma tiltedBackward_time {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c)
    {T t : ℝ} (ht : t < T) (x : ℝ) :
    HasDerivAt (fun u => tiltedBackward c T f g u x) (tiltedBackwardRate c T f g t x) t := by
  have hh := ((varianceTilted_equation hf hLip hg hc (sub_nonneg.mpr ht.le) x).hasDerivAt
    (Ici_mem_nhds (sub_pos.mpr ht))).comp t ((hasDerivAt_id t).const_sub T)
  convert hh using 1 <;> first | rfl | (dsimp [tiltedBackwardRate,tiltedRate];ring)

lemma tiltedBackward_integrated_rate {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c)
    {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    tiltedBackward c T f g b x-tiltedBackward c T f g a x =
      ∫ t in a..b, tiltedBackwardRate c T f g t x := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact ((tiltedBackward_continuous hf hLip hg hc T).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro t ht
    exact tiltedBackward_time hf hLip hg hc (ht.2.trans_le hb) x
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (tiltedBackwardRate_continuousOn hf hLip hg hc T).comp
      (f := fun t : ℝ => (t,x)) (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨⟨ha.trans ht.1,ht.2.trans hb⟩,mem_univ _⟩)

lemma tiltedBackward_terminal (c T : ℝ) (f g : ℝ → ℝ) (x : ℝ) : tiltedBackward c T f g T x=g x := by
  simp only [tiltedBackward,sub_self,varianceTilted,varianceHeat_zero]
  exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.IntegralTimeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
open Heat

lemma BoundedSmoothFamily_lipschitz {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (F t) := by
  obtain ⟨L,hL⟩ := hF.deriv.bound
  refine ⟨L,fun t => lipschitzWith_of_nnnorm_deriv_le
    ((hF.regular t).smooth.differentiable (by simp)) (fun x => ?_)⟩
  exact_mod_cast hL t x

lemma time_integral_spatial_bound {D : ℝ → ℝ → ℝ} (hD : BoundedSmoothFamily D)
    {L : ℝ≥0} (hL : ∀ t, LipschitzWith L (D t)) (a b x z : ℝ) :
    |(∫ r in a..b, D r z)-(∫ r in a..b, D r x)| ≤
      (L:ℝ)*|b-a| *|z-x| := by
  rw [← intervalIntegral.integral_sub (hD.intervalIntegrable z a b) (hD.intervalIntegrable x a b)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => D r z-D r x) (C := (L:ℝ)*|z-x|)
    (fun r (_hr : r ∈ uIoc a b) => by
      simpa only [Real.norm_eq_abs] using (hL r).norm_sub_le z x)
  simpa only [Real.norm_eq_abs,mul_right_comm] using hh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_family_comp [IsFiniteMeasure P] {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (t : ℝ) {Y : Ω → ℝ} (hY : Measurable Y) :
    Integrable (fun ω => F t (Y ω)) P := by
  obtain ⟨C,hC⟩ := hF.bound
  exact Integrable.of_bound (((hF.regular t).smooth.continuous.measurable).comp hY).aestronglyMeasurable
    C (Eventually.of_forall (fun ω => hC t (Y ω)))

lemma measurable_family_integral {D : ℝ → ℝ → ℝ} (hD : BoundedSmoothFamily D) (a b : ℝ) :
    Measurable (fun x => ∫ r in a..b, D r x) :=
  (show Differentiable ℝ (fun x => ∫ r in a..b, D r x) from
    fun x => (hD.hasDerivAt_integral a b x).differentiableAt).continuous.measurable

lemma integrable_family_integral_comp [IsFiniteMeasure P] {D : ℝ → ℝ → ℝ}
    (hD : BoundedSmoothFamily D) (a b : ℝ) {Y : Ω → ℝ} (hY : Measurable Y) :
    Integrable (fun ω => ∫ r in a..b, D r (Y ω)) P := by
  obtain ⟨C,hC⟩ := hD.bound
  apply Integrable.of_bound ((measurable_family_integral hD a b).comp hY).aestronglyMeasurable
    ((C:ℝ)*|b-a|)
  filter_upwards [] with ω
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hC r (Y ω))

lemma expected_integral_time_step {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0)
    {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {F D : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hD : BoundedSmoothFamily D)
    (C₁ C₂ C₃ L : ℝ≥0) (hC₁ : ∀ x, |deriv (F s) x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv (F s)) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 (F s) x| ≤ C₃)
    (hL : ∀ r, LipschitzWith L (D r))
    (he : ∀ x, F ((s:ℝ)+(h:ℝ)) x-F s x = ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r x) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+A ω) ∂P)-
      (∫ ω, F s (Y ω) ∂P)-(∫ ω, deriv (F s) (Y ω)*A ω ∂P)-
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P)| ≤
      (C₃:ℝ)/6*((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment)+
      (C₂:ℝ)*(M:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ))+
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  let Z (ω : Ω) := Y ω+(B (s+h) ω-B s ω)+A ω
  have hZm : Measurable Z := (hYm.add ((hm _).sub (hm _))).add hA
  have hd : Integrable (fun ω => B (s+h) ω-B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  let R (ω : Ω) := F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)-
    ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)
  have hiR : Integrable R P :=
    ((integrable_family_comp hF _ hZm).sub (integrable_family_comp hF _ hZm)).sub
      (integrable_family_integral_comp hD _ _ hYm)
  have hRb (ω : Ω) : |R ω| ≤ (L:ℝ)*(h:ℝ)*(|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) := by
    dsimp only [R]
    rw [he]
    have hi := time_integral_spatial_bound hD hL (s:ℝ) ((s:ℝ)+(h:ℝ)) (Y ω) (Z ω)
    rw [add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] at hi
    apply hi.trans
    have hz : |Z ω-Y ω| ≤ |B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ) := by
      have heq : Z ω-Y ω = (B (s+h) ω-B s ω)+A ω := by dsimp [Z]; ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add_right (hAb ω) _)
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg L.coe_nonneg h.coe_nonneg)
  have hRe : |∫ ω, R ω ∂P| ≤
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (L:ℝ)*(h:ℝ)*(|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) ∂P :=
        integral_mono hiR.abs ((hd.abs.add (integrable_const _)).const_mul _) hRb
      _ = _ := by
        rw [integral_const_mul,integral_add hd.abs (integrable_const _),increment_abs_first hB s h]
        simp
  have hRi : (∫ ω, R ω ∂P) =
      (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P)-(∫ ω, F s (Z ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P) := by
    have h1 := integrable_family_comp (P := P) hF ((s:ℝ)+(h:ℝ)) hZm
    have h0 := integrable_family_comp (P := P) hF (s:ℝ) hZm
    have hdI := integrable_family_integral_comp (P := P) hD (s:ℝ) ((s:ℝ)+(h:ℝ)) hYm
    calc
      _ = (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω) ∂P)-
          (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P) :=
        integral_sub (h1.sub h0) hdI
      _ = _ := by rw [integral_sub h1 h0]

  have hS := expected_control_step hB hm s h hY hYi hA M hAb
    ((hF.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) C₁ C₂ C₃ hC₁ hC₂ hC₃
  rw [hRi] at hRe
  have ht := (abs_add_le
    ((∫ ω, F s (Z ω) ∂P)-(∫ ω, F s (Y ω) ∂P)-
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P)-(h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P))
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P)-(∫ ω, F s (Z ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P))).trans
        (add_le_add hS hRe)
  convert ht using 1 <;> try rfl
  congr 1
  ring

end ZeroTemperatureSK.WeakIto

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma time_average_bound {f : ℝ → ℝ} {C a b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, |f t| ≤ C) : |(∫ t in a..b, f t)/(b-a)| ≤ C := by
  by_cases he : b=a
  · simp [he,hC]
  have hp : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr he)
  rw [abs_div,div_le_iff₀ hp]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := C) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)

lemma time_average_tendsto_right {f : ℝ → ℝ} (hm : Measurable f) (a : ℝ)
    (hc : ContinuousWithinAt f (Ioi a) a) :
    Tendsto (fun b => (∫ t in a..b, f t)/(b-a)) (𝓝[>] a) (𝓝 (f a)) := by
  have hh := intervalIntegral.integral_hasDerivWithinAt_right
    (a := a) (b := a) (s := Ici a) (t := Ioi a) IntervalIntegrable.refl
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (show a ∉ Ioi a by simp)).mp
    (hh.mono Ioi_subset_Ici_self)
  apply hl.congr
  intro b
  simp only [slope_def_field,intervalIntegral.integral_same,sub_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma measurable_time_integral {f : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2)) (a b : ℝ) :
    Measurable (fun ω => ∫ t in a..b, f t ω) := by
  rw [show (fun ω => ∫ t in a..b, f t ω) =
    (fun ω => (∫ t in Ioc a b, f t ω)-(∫ t in Ioc b a, f t ω)) from rfl]
  exact hm.stronglyMeasurable.integral_prod_left.measurable.sub
    hm.stronglyMeasurable.integral_prod_left.measurable

lemma expected_time_average_tendsto_right [IsFiniteMeasure P] {f : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ω, |f t ω| ≤ C) (a : ℝ)
    (hc : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω) (Ioi a) a) :
    Tendsto (fun b => ∫ ω, (∫ t in a..b, f t ω)/(b-a) ∂P)
      (𝓝[>] a) (𝓝 (∫ ω, f a ω ∂P)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun b => ((measurable_time_integral hm a b).div_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun b => Eventually.of_forall fun ω =>
      time_average_bound hC (fun t => hb t ω)
  · exact integrable_const C
  · filter_upwards [hc] with ω hω
    exact time_average_tendsto_right (hm.comp measurable_prodMk_right) a hω

end ZeroTemperatureSK.WeakIto

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.BoundedDiffusionProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_measurable_at (ℱ : Filtration ℝ≥0 mΩ) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsProgressive ℱ X) (t : ℝ≥0) : Measurable[ℱ t] (X t) :=
  hX.adapted t

namespace BoundedLipschitzDrift
variable (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)

lemma solution_adapted (t : ℝ≥0) :
    Measurable[Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable) t]
      (b.solution W.driver t) :=
  progressive_measurable_at _ (b.solution_progressive _ W.driver_progressive) t

lemma solution_measurable (t : ℝ≥0) : Measurable (b.solution W.driver t) :=
  (b.solution_adapted W t).mono
    ((Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)).le t) le_rfl

lemma solution_integrable (t : ℝ≥0) : Integrable (b.solution W.driver t) W.law := by
  let := W.isProbability
  have hc : Integrable (b.correction W.driver t) W.law := by
    apply Integrable.of_bound
      ((progressive_joint_measurable _ (b.correction_progressive _ W.driver_progressive)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((b.bound:ℝ)*(t:ℝ))
    exact Eventually.of_forall (b.correction_bound _ W.driver_progressive t)
  have hd : Integrable (W.driver t) W.law :=
    (W.brownian.integrable_eval t).congr (W.driver_indistinguishable.mono (fun _ h => (h t).symm))
  exact hd.add hc

lemma solution_continuous_ae : ∀ᵐ ω ∂W.law, Continuous (fun t => b.solution W.driver t ω) := by
  filter_upwards [W.driver_continuous] with ω hω
  exact b.solution_continuous _ W.driver_progressive hω

lemma pathDrift_measurable : Measurable (fun p : ℝ × Ω => b.pathDrift W p.1 p.2) := by
  have hx := progressive_joint_measurable _ (b.solution_progressive _ W.driver_progressive)
  exact b.measurable.comp
    ((measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk
      (hx.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)))

lemma pathDrift_bound (t : ℝ) (ω : Ω) : |b.pathDrift W t ω| ≤ b.bound := b.bounded _ _

lemma pathDrift_integrable (a c : ℝ) (ω : Ω) :
    IntervalIntegrable (fun t => b.pathDrift W t ω) volume a c := by
  apply (intervalIntegrable_const (c := (b.bound:ℝ))).mono_fun
    ((b.pathDrift_measurable W).comp measurable_prodMk_right).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg b.bound.coe_nonneg] using b.pathDrift_bound W t ω)

lemma displacement_measurable (s t : ℝ) : Measurable (b.displacement W s t) :=
  measurable_time_integral (b.pathDrift_measurable W) s t

lemma displacement_bound (s t : ℝ) (ω : Ω) :
    |b.displacement W s t ω| ≤ (b.bound:ℝ)*|t-s| :=
  intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => b.pathDrift W r ω) (C := (b.bound:ℝ))
    (fun r _ => b.pathDrift_bound W r ω)

lemma solution_increment (s h : ℝ≥0) : ∀ᵐ ω ∂W.law,
    b.solution W.driver (s+h) ω = b.solution W.driver s ω+
      (W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω := by
  filter_upwards [W.driver_indistinguishable] with ω hω
  rw [b.solution_eq _ W.driver_progressive (s+h),b.solution_eq _ W.driver_progressive s,hω,hω]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (b.pathDrift_integrable W 0 s ω) (b.pathDrift_integrable W s (s+h) ω)
  change (∫ r in (0:ℝ)..(s:ℝ), b.pathDrift W r ω)+b.displacement W s (s+h) ω =
    ∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), b.pathDrift W r ω at he
  change W.B (s+h) ω+(∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), b.pathDrift W r ω) =
    W.B s ω+(∫ r in (0:ℝ)..(s:ℝ), b.pathDrift W r ω)+(W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω
  rw [← he]
  ring

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.RightGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat
variable {Ω : Type*} [MeasurableSpace Ω]

theorem expected_hasDerivWithinAt_right (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F D : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) (hD : BoundedSmoothFamily D)
    {T : ℝ} (he : ∀ a c, 0 ≤ a → a ≤ c → c ≤ T → ∀ x,
      F c x-F a x = ∫ r in a..c, D r x)
    (s : ℝ≥0) (hsT : (s:ℝ) < T)
    (hDr : ∀ x, ContinuousWithinAt (fun r => D r x) (Ioi (s:ℝ)) s)
    (hbr : ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ω) (Ioi (s:ℝ)) s) :
    HasDerivWithinAt
      (fun t : ℝ => ∫ ω, F t (b.solution W.driver (Real.toNNReal t) ω) ∂W.law)
      ((∫ ω, deriv (F s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
        (1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (b.solution W.driver s ω) ∂W.law)+
        (∫ ω, D s (b.solution W.driver s ω) ∂W.law)) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  let Y := b.solution W.driver s
  have hYm : Measurable Y := b.solution_measurable W s
  obtain ⟨C₁,hC₁⟩ := hF.deriv.bound
  obtain ⟨C₂,hC₂⟩ := hF.deriv.deriv.bound
  obtain ⟨C₃,hC₃⟩ := hF.bounds 3
  obtain ⟨Ct,hCt⟩ := hD.bound
  obtain ⟨L,hL⟩ := BoundedSmoothFamily_lipschitz hD
  let Q (t : ℝ) := ∫ ω, F t (b.solution W.driver (Real.toNNReal t) ω) ∂W.law
  let H : ℝ := ∫ ω, deriv (deriv (F s)) (Y ω) ∂W.law
  let A (t : ℝ) := ∫ ω, deriv (F s) (Y ω)*b.displacement W s t ω ∂W.law
  let J (t : ℝ) := ∫ ω, (∫ r in (s:ℝ)..t, D r (Y ω)) ∂W.law
  let K (t : ℝ) := A t/(t-s)+(1/2:ℝ)*H+J t/(t-s)
  have hcoeff : Measurable (fun ω => deriv (F s) (Y ω)) :=
    ((hF.deriv.regular s).smooth.continuous.measurable).comp hYm
  have hma : Measurable (fun p : ℝ × Ω => deriv (F s) (Y p.2)*b.pathDrift W p.1 p.2) :=
    (hcoeff.comp measurable_snd).mul (b.pathDrift_measurable W)
  have halim := expected_time_average_tendsto_right (P := W.law) hma
    (mul_nonneg C₁.coe_nonneg b.bound.coe_nonneg)
    (fun r ω => by
      rw [abs_mul]
      exact mul_le_mul (hC₁ s (Y ω)) (b.pathDrift_bound W r ω) (abs_nonneg _) C₁.coe_nonneg)
    (s:ℝ) (by
      filter_upwards [hbr] with ω hω
      exact continuousWithinAt_const.mul hω)
  have hAlim : Tendsto (fun t => A t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ ω, deriv (F s) (Y ω)*b.pathDrift W s ω ∂W.law)) := by
    convert halim using 1 <;> try rfl
    funext t
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hmj : Measurable (fun p : ℝ × Ω => D p.1 (Y p.2)) :=
    hD.measurable.comp (measurable_fst.prodMk (hYm.comp measurable_snd))
  have hjlim := expected_time_average_tendsto_right (P := W.law) hmj Ct.coe_nonneg
    (fun r ω => hCt r (Y ω)) (s:ℝ) (Eventually.of_forall (fun ω => hDr (Y ω)))
  have hJlim : Tendsto (fun t => J t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ ω, D s (Y ω) ∂W.law)) := by
    convert hjlim using 1 <;> try rfl
    funext t
    exact (integral_div (t-(s:ℝ)) _).symm
  have hKlim := (hAlim.add_const ((1/2:ℝ)*H)).add hJlim
  let E (t : ℝ) := (C₃:ℝ)/6*(Real.sqrt (t-s)*normalThirdMoment)+
    (C₂:ℝ)*(b.bound:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))+
    (L:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))
  have hzero : Tendsto (fun t : ℝ => t-(s:ℝ)) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => t) (𝓝[>] (s:ℝ)) (𝓝 (s:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hh.sub_const (s:ℝ)
  have hsqrt := hzero.sqrt
  have hElim : Tendsto E (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hbase := (hsqrt.mul_const normalFirstMoment).add (hzero.const_mul (b.bound:ℝ))
    simpa only [E,Real.sqrt_zero,zero_mul,mul_zero,add_zero] using
      (((hsqrt.mul_const normalThirdMoment).const_mul ((C₃:ℝ)/6)).add
        (hbase.const_mul ((C₂:ℝ)*(b.bound:ℝ)))).add (hbase.const_mul (L:ℝ))
  have hbound : ∀ᶠ t in 𝓝[>] (s:ℝ), |slope Q s t-K t| ≤ E t := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with t hst htT
    have hp : 0 < t-(s:ℝ) := sub_pos.mpr hst
    let h := Real.toNNReal (t-(s:ℝ))
    have hcoe : (h:ℝ)=t-(s:ℝ) := Real.coe_toNNReal _ hp.le
    have htime : (s:ℝ)+(h:ℝ)=t := by rw [hcoe]; ring
    have hnn : s+h=Real.toNNReal t := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add,htime,Real.coe_toNNReal _ (s.coe_nonneg.trans hst.le)]
    have hstep := expected_integral_time_step W.brownian.toIsPreBrownianReal W.measurable s h
      (b.solution_adapted W s) (b.solution_integrable W s)
      (b.displacement_measurable W s (s+h)) b.bound
      (fun ω => by
        have hb := b.displacement_bound W (s:ℝ) ((s+h:ℝ≥0):ℝ) ω
        simpa only [NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] using hb)
      hF hD C₁ C₂ C₃ L (hC₁ s) (hC₂ s) (hC₃ s) hL
      (he s ((s:ℝ)+(h:ℝ)) s.coe_nonneg (by linarith [h.coe_nonneg]) (by rw [htime]; exact htT.le))
    have hsol : (∫ ω, F ((s:ℝ)+(h:ℝ))
        (b.solution W.driver s ω+(W.B (s+h) ω-W.B s ω)+b.displacement W s (s+h) ω) ∂W.law) = Q t := by
      unfold Q
      apply integral_congr_ae
      filter_upwards [b.solution_increment W s h] with ω hω
      rw [← hω,hnn,htime]
    rw [hsol] at hstep
    have hqs : (∫ ω, F s (b.solution W.driver s ω) ∂W.law) = Q s := by simp only [Q,Real.toNNReal_coe]
    rw [hqs] at hstep
    have hat : (∫ ω, deriv (F s) (b.solution W.driver s ω)*b.displacement W s (s+h) ω ∂W.law) = A t := by
      simp only [A,Y,htime]
    rw [hat,htime,hcoe] at hstep
    change |Q t-Q s-A t-(t-(s:ℝ))/2*H-J t| ≤ _ at hstep
    have heq : slope Q s t-K t = (Q t-Q s-A t-(t-(s:ℝ))/2*H-J t)/(t-s) := by
      rw [slope_def_field]
      dsimp only [K]
      field_simp
      ring
    rw [heq,abs_div,abs_of_pos hp,div_le_iff₀ hp]
    convert hstep using 1 <;> try rfl
    all_goals try dsimp only [E]
    all_goals first | rfl | ring
  have herr : Tendsto (fun t => slope Q s t-K t) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hElim
    simpa only [Real.norm_eq_abs] using hbound
  have hh := herr.add hKlim
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (s:ℝ) ∉ Ioi (s:ℝ) by simp)).mpr
  convert hh using 1 <;> try rfl
  · funext t
    dsimp only [K] at *
    ring
  · simp only [zero_add,H,Y]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.TiltedTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma Heat.varianceGradient_joint_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (varianceLogHeat c p.1 f) p.2)=
      fun p => varianceTilted c p.1 f (deriv f) p.2 :=
    funext (fun p => congrFun (deriv_varianceLogHeat_tilted hf hLip hc p.1) p.2)
  rw [he]
  exact varianceTilted_joint_continuous hf hLip hf.deriv_bounded hc

lemma Heat.tiltedBackwardRate_continuous {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    Continuous (fun p : ℝ × ℝ => tiltedBackwardRate c T f g p.1 p.2) := by
  have hU := varianceTilted_family hf hLip hg hc
  have hUc := varianceTilted_joint_continuous hf hLip hg hc
  have hUx := hU.continuous_iteratedDeriv hUc 1
  have hUxx := hU.continuous_iteratedDeriv hUc 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hUx hUxx
  have hr : Continuous (fun p : ℝ × ℝ => tiltedRate c f g p.1 p.2) :=
    (continuous_const.mul hUxx).add
      ((continuous_const.mul (varianceGradient_joint_continuous hf hLip hc)).mul hUx)
  change Continuous (fun p : ℝ × ℝ => -tiltedRate c f g (T-p.1) p.2)
  exact hr.neg.comp (f := fun p : ℝ × ℝ => (T-p.1,p.2))
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

lemma drift_tilted_path_continuous_right (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f)
    {c a T : ℝ} (hc : 0 ≤ c)
    (hmatch : ∀ t ∈ Ico a T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x)
    (s : ℝ≥0) (has : a ≤ s) (hsT : (s:ℝ) < T) :
    ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ω) (Ioi (s:ℝ)) s := by
  filter_upwards [b.solution_continuous_ae W] with ω hω
  have hβ : Continuous (fun t : ℝ => c*deriv (varianceLogHeat c (T-t) f)
      (b.solution W.driver (Real.toNNReal t) ω)) :=
    continuous_const.mul ((varianceGradient_joint_continuous hf hLip hc).comp
      ((continuous_const.sub continuous_id).prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal))))
  apply hβ.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with r hr hrT
    unfold BoundedLipschitzDrift.pathDrift
    rw [Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le)]
    exact hmatch r ⟨has.trans hr.le,hrT⟩ _
  · unfold BoundedLipschitzDrift.pathDrift
    rw [Real.toNNReal_coe]
    exact hmatch s ⟨has,hsT⟩ _

theorem expected_tiltedBackward_right_zero (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f g : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c a T : ℝ} (hc : 0 ≤ c)
    (hmatch : ∀ t ∈ Ico a T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x)
    (s : ℝ≥0) (has : a ≤ s) (hsT : (s:ℝ) < T) :
    HasDerivWithinAt (fun t : ℝ => ∫ ω, tiltedBackward c T f g t
      (b.solution W.driver (Real.toNNReal t) ω) ∂W.law) 0 (Ioi (s:ℝ)) s := by
  let := W.isProbability
  have hF := tiltedBackward_family hf hLip hg hc T
  have hD := tiltedBackwardRate_family hf hLip hg hc T
  have hgen := expected_hasDerivWithinAt_right W b hF hD
    (fun a d ha had hd => tiltedBackward_integrated_rate hf hLip hg hc ha had hd)
    s hsT (fun x => ((tiltedBackwardRate_continuous hf hLip hg hc T).comp
      (continuous_id.prodMk continuous_const)).continuousWithinAt)
    (drift_tilted_path_continuous_right W b hf hLip hc hmatch s has hsT)
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ω => deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω) W.law := by
    apply (integrable_family_comp hF.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => b.pathDrift_bound W s ω)
  have hi2 := integrable_family_comp (P := W.law) hF.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) hD (s:ℝ) hx
  have he : (∫ ω, deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
      (1/2:ℝ)*(∫ ω, deriv (deriv (tiltedBackward c T f g s)) (b.solution W.driver s ω) ∂W.law)+
      (∫ ω, tiltedBackwardRate c T f g s (b.solution W.driver s ω) ∂W.law)=0 := by
    have hsum := integral_add (hi1.add (hi2.const_mul (1/2:ℝ))) hi3
    dsimp only [Pi.add_apply] at hsum
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),← hsum]
    have hz : (fun ω => deriv (tiltedBackward c T f g s) (b.solution W.driver s ω)*b.pathDrift W s ω+
        (1/2:ℝ)*deriv (deriv (tiltedBackward c T f g s)) (b.solution W.driver s ω)+
        tiltedBackwardRate c T f g s (b.solution W.driver s ω))=fun _ => 0 := by
      funext ω
      unfold tiltedBackward
      simp only [BoundedLipschitzDrift.pathDrift,Real.toNNReal_coe,
        hmatch s ⟨has,hsT⟩,tiltedBackwardRate,tiltedRate]
      ring
    rw [hz,integral_zero]
  rwa [he] at hgen

theorem expected_transition_tiltedMean (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {f g : ℝ → ℝ} {K : ℝ≥0} (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g)
    {c : ℝ} (hc : 0 ≤ c) {a T : ℝ≥0} (haT : a ≤ T)
    (hmatch : ∀ t ∈ Ico (a:ℝ) T, ∀ x, b.f t x=c*deriv (varianceLogHeat c (T-t) f) x) :
    (∫ ω, g (b.solution W.driver T ω) ∂W.law)=
      ∫ ω, varianceTilted c ((T:ℝ)-a) f g (b.solution W.driver a ω) ∂W.law := by
  have hcF : Continuous (fun r : ℝ =>
      ∫ ω, tiltedBackward c T f g r (b.solution W.driver (Real.toNNReal r) ω) ∂W.law) := by
    let := W.isProbability
    have hF := tiltedBackward_family hf hLip hg hc T
    obtain ⟨C,hC⟩ := hF.bound
    apply continuous_of_dominated (bound := fun _ => (C:ℝ))
    · intro r
      exact ((hF.regular r).smooth.continuous.measurable.comp
        (b.solution_measurable W (Real.toNNReal r))).aestronglyMeasurable
    · intro r
      exact Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hC r (b.solution W.driver (Real.toNNReal r) ω))
    · exact integrable_const _
    · filter_upwards [b.solution_continuous_ae W] with ω hω
      exact (tiltedBackward_continuous hf hLip hg hc T).comp
        (continuous_id.prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (show (a:ℝ) ≤ T from haT)
    hcF.continuousOn (f' := fun _ => (0:ℝ)) (fun r hr => by
      have hh := expected_tiltedBackward_right_zero W b hf hLip hg hc hmatch (Real.toNNReal r)
        (by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)];exact hr.1.le)
        (by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)];exact hr.2)
      simpa only [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1.le)] using hh)
    (intervalIntegrable_const)
  simp only [intervalIntegral.integral_zero,Real.toNNReal_coe,tiltedBackward_terminal] at hi
  exact sub_eq_zero.mp hi.symm

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.FiniteTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma Heat.varianceLogHeat_add {f : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K f)
    {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    varianceLogHeat c (a+b) f=varianceLogHeat c a (varianceLogHeat c b f) := by
  funext x
  rw [varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable,
    varianceLogHeat_eq_logSemigroup_toNNReal (varianceLogHeat_lipschitz hLip hc b).continuous.measurable]
  have he : varianceLogHeat c b f=logSemigroup c (Real.toNNReal b) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable c b)
  rw [he,Real.toNNReal_add ha hb,logSemigroup_add hLip]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.TerminalTailValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto Nonuniform
variable {Ω : Type*} [MeasurableSpace Ω]

lemma abs_lipschitz : LipschitzWith (1:ℝ≥0) (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

lemma plateau_grid_error_zero (γ : OrderParameter) {a c t : ℝ} (hc0 : 0 ≤ c)
    (ht0 : 0 ≤ t) (hat : a < t) (ht1 : t < 1) (hc : ∀ s ∈ Ioo a 1, extend γ.val s=c) :
    gridError (fun _ => Real.toNNReal (1-t)) (fun _ => ⟨c,hc0⟩) (fun r => extend γ.val (t+r)) 1=0 := by
  simp only [gridError,Finset.sum_range_one,time_zero,time_succ,zero_add,NNReal.coe_zero,
    Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
  have he : (∫ r in (0:ℝ)..(1-t), |c-extend γ.val (t+r)|)=∫ _r in (0:ℝ)..(1-t), (0:ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (sub_nonneg.mpr ht1.le)
    intro r hr
    change |c-extend γ.val (t+r)|=0
    have htr : t+r ∈ Ico (0:ℝ) 1 := ⟨add_nonneg ht0 hr.1.le,by linarith [hr.2]⟩
    have hval : γ.val ⟨t+r,htr⟩=c := by
      simpa only [extend,dite_eq_left htr] using hc (t+r) ⟨by linarith [hr.1],htr.2⟩
    rw [extend,dite_eq_left htr,hval,sub_self,abs_zero]
  change (∫ r in (0:ℝ)..(1-t), |c-extend γ.val (t+r)|)=0
  rw [he,intervalIntegral.integral_zero]

theorem value_on_terminal_plateau (W : BrownianSystem Ω) (γ : OrderParameter) {a c t : ℝ}
    (hc0 : 0 ≤ c) (ht0 : 0 ≤ t) (hat : a < t) (ht1 : t < 1)
    (hc : ∀ s ∈ Ioo a 1, extend γ.val s=c) :
    value W γ t=varianceLogHeat c (1-t) abs := by
  funext x
  rw [varianceLogHeat_eq_logSemigroup_toNNReal measurable_abs]
  let H : ℕ → ℝ≥0 := fun _ => Real.toNNReal (1-t)
  let C : ℕ → ℝ≥0 := fun _ => ⟨c,hc0⟩
  have hH : (time H 1:ℝ)=1-t := by simp only [time_succ,time_zero,zero_add,H,Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
  have hb (n : ℕ) : |value W γ t x-logSemigroup c (Real.toNNReal (1-t)) abs x| ≤
      (2*Real.log 2)*(approxMesh n:ℝ) := by
    let M : ℝ := ((n+1:ℕ):ℝ)
    have hM : 0 < M := by dsimp [M];positivity
    have he (z : ℝ) : |softAbs M z-abs z| ≤ Real.log 2/M := by
      rw [abs_of_nonneg (softAbs_bounds hM z).1]
      exact (softAbs_bounds hM z).2
    have hv := cascadeV_value_error W γ t x ht0 ht1.le H C 1 hH
      (regularDatum_softAbs hM.ne') (softAbs_lipschitz hM.ne') he
    rw [plateau_grid_error_zero γ hc0 ht0 hat ht1 hc] at hv
    simp only [cascadeV,C,H,mul_zero,add_zero] at hv
    change |logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x-value W γ t x| ≤ Real.log 2/M at hv
    have hv' : |value W γ t x-logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x| ≤ Real.log 2/M := by
      simpa only [abs_sub_comm] using hv
    have hs := logSemigroup_terminal_stability (softAbs_lipschitz hM.ne') abs_lipschitz hc0 he (Real.toNNReal (1-t)) x
    have htri := abs_sub_le (value W γ t x) (logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x)
      (logSemigroup c (Real.toNNReal (1-t)) abs x)
    have heM : Real.log 2/M+Real.log 2/M=(2*Real.log 2)*(approxMesh n:ℝ) := by
      simp only [M,approxMesh,NNReal.coe_inv,NNReal.coe_natCast]
      ring
    linarith
  have hz : Tendsto (fun n => (2*Real.log 2)*(approxMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul approxMesh_limit (a := 2*Real.log 2)
  have he := ge_of_tendsto hz (Eventually.of_forall hb)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

lemma value_plateau_semigroup (W : BrownianSystem Ω) (γ : OrderParameter) {a c s T : ℝ}
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (has : a < s) (hsT : s ≤ T) (hT1 : T < 1)
    (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c) :
    value W γ s=varianceLogHeat c (T-s) (value W γ T) := by
  rw [value_on_terminal_plateau W γ hc0 hs0 has (hsT.trans_lt hT1) hc,
    value_on_terminal_plateau W γ hc0 (hs0.trans hsT) (has.trans_le hsT) hT1 hc,
    ← varianceLogHeat_add abs_lipschitz hc0 (sub_nonneg.mpr hsT) (sub_nonneg.mpr hT1.le)]
  congr 1
  ring

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.PicardUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (b : BoundedLipschitzDrift)

lemma correction_unique_on (ℱ : Filtration ℝ≥0 mΩ) {B Z : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (hZ : IsProgressive ℱ Z) (T : ℝ≥0) (ω : Ω)
    (hfix : ∀ t ≤ T, Z t ω = timePrimitive (b.action B Z) t ω) :
    ∀ t ≤ T, b.correction B t ω = Z t ω := by
  have hbase (t : ℝ≥0) (ht : t ≤ T) :
      |b.correction B t ω-Z t ω| ≤ 2*(b.bound:ℝ)*Real.exp (b.rate*t) := by
    have hzb : |Z t ω| ≤ (b.bound:ℝ)*(t:ℝ) := by
      rw [hfix t ht]
      exact timePrimitive_bound ℱ (b.action_progressive ℱ hB hZ) (b.action_bound _ _) _ _
    have htt : (t:ℝ) ≤ Real.exp (b.rate*t) := by
      have hh : (t:ℝ) ≤ b.rate*t := by nlinarith [b.one_le_rate,t.coe_nonneg]
      linarith [Real.add_one_le_exp (b.rate*t)]
    apply (abs_sub _ _).trans
    nlinarith [b.correction_bound ℱ hB t ω,
      mul_le_mul_of_nonneg_left htt b.bound.coe_nonneg]
  have hest (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      |b.correction B t ω-Z t ω| ≤ 2*(b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t) := by
    induction n generalizing t with
    | zero => simpa only [pow_zero,mul_one] using hbase t ht
    | succ n hn =>
      rw [b.correction_eq_integral ℱ hB t ω,hfix t ht]
      have hh := b.timePrimitive_action_sub_estimate ℱ hB (b.correction_progressive ℱ hB) hZ
        (show 0 ≤ 2*(b.bound:ℝ)*(1/2:ℝ)^n by positivity) t ω (fun s hs => hn s (hs.trans ht))
      convert hh using 1 <;> try rfl
      rw [pow_succ]
      ring
  intro t ht
  have hh : Tendsto (fun n : ℕ => 2*(b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2:ℝ)<1))
        (a := 2*(b.bound:ℝ))).mul_const (Real.exp (b.rate*t))
  have hz : |b.correction B t ω-Z t ω| ≤ 0 :=
    ge_of_tendsto hh (Eventually.of_forall (fun n => hest n t ht))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

lemma solution_eq_of_agree (b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0)
    (he : ∀ t : ℝ≥0, t ≤ T → ∀ x, b.f t x = b'.f t x) (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    b.solution B t ω = b'.solution B t ω := by
  have hu := b.correction_unique_on ℱ hB (b'.correction_progressive ℱ hB) T ω
  apply congrArg (B t ω+ ·)
  apply hu _ t ht
  intro s hs
  rw [b'.correction_eq_integral ℱ hB s ω]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le s.coe_nonneg] at hr
  exact (he (Real.toNNReal r) ((Real.toNNReal_le_iff_le_coe.mpr hr.2).trans hs) _).symm

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.CompactDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactDrift_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T t : ℝ}
    (ht : t ∈ Icc (0:ℝ) T) (x : ℝ) :
    compactDrift W γ T t x = extend γ.val t*gradient W γ t x := by
  simp only [compactDrift,compactCoeff,compactGradient,stripClamp_eq ht]

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

lemma diffusionHorizon_tendsto : Tendsto diffusionHorizon atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1-1/((n+2:ℕ):ℝ)) atTop (𝓝 1)
  have hh := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 2)
  simpa only [diffusionHorizon,sub_zero,Function.comp_apply] using tendsto_const_nhds.sub hh (a := (1:ℝ))

lemma eventually_le_diffusionHorizon {t : ℝ} (ht : t < 1) :
    ∀ᶠ n : ℕ in atTop, t ≤ diffusionHorizon n :=
  (diffusionHorizon_tendsto.eventually (eventually_gt_nhds ht)).mono (fun _ h => h.le)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma stripDrift_eq (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (T:ℝ)) (x : ℝ) :
    (stripDrift W γ T).f t x = extend γ.val t*gradient W γ t x := compactDrift_eq W γ ht x

lemma localDiffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (localDiffusion W γ n) :=
  (stripDrift W γ (diffusionHorizonTime n)).solution_progressive _ W.driver_progressive

lemma localDiffusion_agree (W : BrownianSystem Ω) (γ : OrderParameter) (m n : ℕ)
    (t : ℝ≥0) (hm : (t:ℝ) ≤ diffusionHorizon m) (hn : (t:ℝ) ≤ diffusionHorizon n) (ω : Ω) :
    localDiffusion W γ m t ω = localDiffusion W γ n t ω := by
  apply (stripDrift W γ (diffusionHorizonTime m)).solution_eq_of_agree
    (stripDrift W γ (diffusionHorizonTime n)) _ W.driver_progressive t _ t le_rfl ω
  intro s hs x
  have hst : (s:ℝ) ≤ (t:ℝ) := hs
  rw [stripDrift_eq W γ _ ⟨s.coe_nonneg,hst.trans hm⟩,
    stripDrift_eq W γ _ ⟨s.coe_nonneg,hst.trans hn⟩]

lemma rawDiffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (rawDiffusion W γ) := by
  intro t
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ t)]
      (fun p : Iic t × Ω => localDiffusion W γ n p.1 p.2) :=
    (localDiffusion_progressive W γ n t).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ t
  exact (StronglyMeasurable.limUnder hm).measurable

lemma rawDiffusion_eq_local (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ diffusionHorizon n) (ω : Ω) :
    rawDiffusion W γ t ω = localDiffusion W γ n t ω := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_diffusionHorizon (ht.trans_lt (diffusionHorizon_mem n).2)] with m hm
  exact localDiffusion_agree W γ n m t ht hm ω

lemma rawDiffusion_eq_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ≥0) (ht : (t:ℝ) < 1) (ω : Ω) :
    rawDiffusion W γ t ω = W.driver t ω+∫ s in (0:ℝ)..(t:ℝ),
      extend γ.val s*gradient W γ s (rawDiffusion W γ (Real.toNNReal s) ω) := by
  obtain ⟨n,hn⟩ := (eventually_le_diffusionHorizon ht).exists
  rw [rawDiffusion_eq_local W γ n t hn]
  rw [localDiffusion, (stripDrift W γ (diffusionHorizonTime n)).solution_eq _ W.driver_progressive]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hsn : ((Real.toNNReal s):ℝ) ≤ diffusionHorizon n := by
    rw [Real.coe_toNNReal _ hs.1]
    exact hs.2.trans hn
  rw [rawDiffusion_eq_local W γ n (Real.toNNReal s) hsn]
  rw [stripDrift_eq W γ _ ⟨(Real.toNNReal s).coe_nonneg,hsn⟩,Real.coe_toNNReal _ hs.1]
  rfl

lemma beforeOneGradient_measurable (W : BrownianSystem Ω) (γ : OrderParameter) :
    Measurable (fun p : ℝ≥0 × ℝ => beforeOneGradient W γ p.1 p.2) := by
  let f (n : ℕ) (p : ℝ≥0 × ℝ) := if (p.1:ℝ) ≤ diffusionHorizon n then
    compactGradient W γ (diffusionHorizon n) p.1 p.2 else 0
  have hm (n : ℕ) : Measurable (f n) := by
    apply Measurable.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const)
    · exact (compactGradient_continuous W γ (diffusionHorizon_mem n).1
        (diffusionHorizon_mem n).2).measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
    · exact measurable_const
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro p
  by_cases hp : (p.1:ℝ) < 1
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_le_diffusionHorizon hp] with n hn
    simp only [f,ite_eq_left hn,beforeOneGradient,ite_eq_left hp,compactGradient,
      stripClamp_eq ⟨p.1.coe_nonneg,hn⟩]
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    have hn : ¬ (p.1:ℝ) ≤ diffusionHorizon n :=
      not_le.mpr ((diffusionHorizon_mem n).2.trans_le (not_lt.mp hp))
    simp only [f,ite_eq_right hn,beforeOneGradient,ite_eq_right hp]

lemma beforeOneGradient_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (x : ℝ) :
    |beforeOneGradient W γ t x| ≤ 1 := by
  unfold beforeOneGradient
  split_ifs with ht
  · exact gradient_abs_le_one W γ _ _ ht.le
  · norm_num

lemma rawFeedback_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (rawFeedback W γ) := by
  intro t
  exact (beforeOneGradient_measurable W γ).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk (rawDiffusion_progressive W γ t))

lemma rawFeedback_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0) (ω : Ω) :
    |rawFeedback W γ t ω| ≤ 1 := beforeOneGradient_bound W γ _ _

lemma rawFeedback_eq (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0)
    (ht : (t:ℝ) < 1) (ω : Ω) :
    rawFeedback W γ t ω = gradient W γ t (rawDiffusion W γ t ω) := by
  simp only [rawFeedback,beforeOneGradient,ite_eq_left ht]

lemma rawDrift_integrable (W : BrownianSystem Ω) (γ : OrderParameter) (ω : Ω) :
    Integrable (fun s : ℝ => extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) := by
  apply γ.integrable.mul_bdd
    (progressive_time_measurable _ (rawFeedback_progressive W γ) ω).aestronglyMeasurable
  exact Eventually.of_forall (fun _ => rawFeedback_bound W γ _ _)

lemma diffusion_progressive (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (diffusion W γ) := by
  have hm : StronglyAdapted (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable))
      (fun t ω => ∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) :=
    fun t => (progressive_integral_measurable _ (rawFeedback_progressive W γ) t γ.measurable_extend).stronglyMeasurable
  have hc (ω : Ω) : Continuous (fun t : ℝ≥0 =>
      ∫ s in (0:ℝ)..(t:ℝ), extend γ.val s*rawFeedback W γ (Real.toNNReal s) ω) :=
    (rawDrift_integrable W γ ω).continuous_primitive 0 |>.comp continuous_subtype_val
  exact W.driver_progressive.add (hm.isStronglyProgressive_of_continuous hc).isProgressive

lemma diffusion_eq_raw (W : BrownianSystem Ω) (γ : OrderParameter) (t : ℝ≥0)
    (ht : (t:ℝ) < 1) (ω : Ω) : diffusion W γ t ω = rawDiffusion W γ t ω := by
  rw [rawDiffusion_eq_integral W γ t ht ω]
  unfold diffusion
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le t.coe_nonneg] at hs
  have hs1 : ((Real.toNNReal s):ℝ) < 1 := by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans_lt ht
  rw [rawFeedback_eq W γ _ hs1,Real.coe_toNNReal _ hs.1]

lemma diffusion_continuous (W : BrownianSystem Ω) (γ : OrderParameter) :
    ∀ᵐ ω ∂W.law, Continuous (fun t => diffusion W γ t ω) := by
  filter_upwards [W.driver_continuous] with ω hc
  exact hc.add ((rawDrift_integrable W γ ω).continuous_primitive 0 |>.comp continuous_subtype_val)

lemma diffusion_zero (W : BrownianSystem Ω) (γ : OrderParameter) (ω : Ω) : diffusion W γ 0 ω = 0 := by
  simp only [diffusion,NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]

theorem diffusion_isDiffusion (W : BrownianSystem Ω) (γ : OrderParameter) :
    IsDiffusion W γ (diffusion W γ) := by
  refine ⟨diffusion_progressive W γ,?_⟩
  filter_upwards [diffusion_continuous W γ,W.driver_indistinguishable] with ω hc hB
  refine ⟨(hc.comp (by fun_prop : Continuous Real.toNNReal)).continuousOn,diffusion_zero W γ ω,?_⟩
  intro t ht
  rw [diffusion,hB,Real.coe_toNNReal _ ht.1]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le ht.1] at hs
  by_cases hs1 : s < 1
  · have hsn : ((Real.toNNReal s):ℝ) < 1 := by rw [Real.coe_toNNReal _ hs.1]; exact hs1
    rw [rawFeedback_eq W γ _ hsn,Real.coe_toNNReal _ hs.1,diffusion_eq_raw W γ _ hsn]
  · have hse : s = 1 := le_antisymm (hs.2.trans ht.2) (not_lt.mp hs1)
    subst s
    have he : extend γ.val 1 = 0 := by simp [extend]
    simp only [he,zero_mul]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.SquareEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactValueRate_eq (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) :
    compactValueRate W γ T t x = -(1/2:ℝ)*deriv (compactGradient W γ T t) x-
      (1/2:ℝ)*compactCoeff γ T t*(compactGradient W γ T t x)^2 := rfl

lemma compactGradient_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T t : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ht0 : 0 ≤ t) (htT : t < T) (x : ℝ) :
    HasDerivWithinAt (fun s => compactGradient W γ T s x)
      (deriv (compactValueRate W γ T t) x) (Ioi t) t := by
  have hh := value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT 1 x
  simp only [iteratedDeriv_one] at hh
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
    simp only [compactGradient,stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,gradient]
  · simp only [compactGradient,stripClamp_eq ⟨ht0,htT.le⟩,gradient]

lemma deriv_compactValueRate (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactValueRate W γ T t) x =
      -(1/2:ℝ)*deriv (deriv (compactGradient W γ T t)) x-
      compactCoeff γ T t*compactGradient W γ T t x*deriv (compactGradient W γ T t) x := by
  have hu := compactGradient_family W γ hT0 hT1
  have hd := ((hu.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hdd := ((hu.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hh := (hdd.const_mul (-(1/2:ℝ))).sub ((hd.pow 2).const_mul ((1/2:ℝ)*compactCoeff γ T t))
  have he : (compactValueRate W γ T t) = (fun x =>
      -(1/2:ℝ)*deriv (compactGradient W γ T t) x-(1/2:ℝ)*compactCoeff γ T t*(compactGradient W γ T t x)^2) :=
    funext (compactValueRate_eq W γ T t)
  rw [he]
  calc
    _ = _ := hh.deriv
    _ = _ := by ring

lemma compactSquare_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactSquare W γ T) :=
  (compactGradient_family W γ hT0 hT1).mul (compactGradient_family W γ hT0 hT1)

lemma compactSquareRate_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactSquareRate W γ T) :=
  ((compactGradient_family W γ hT0 hT1).const_mul 2).mul
    (compactValueRate_family W γ hT0 hT1).deriv

lemma compactSquareRate_right (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    ContinuousWithinAt (fun s => compactSquareRate W γ T s x) (Ioi t) t := by
  have hu := compactGradient_rightSmooth W γ hT0 hT1 0 t x
  have hD := compactValueRate_rightSmooth W γ hT0 hT1 1 t x
  simp only [iteratedDeriv_zero,iteratedDeriv_one] at hu hD
  exact ((continuousWithinAt_const.mul hu).mul hD).mono Ioi_subset_Ici_self

lemma compactSquare_integral_rate (W : BrownianSystem Ω) (γ : OrderParameter)
    {T a b : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    compactSquare W γ T b x-compactSquare W γ T a x =
      ∫ r in a..b, compactSquareRate W γ T r x := by
  apply (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab _ _
    ((compactSquareRate_family W γ hT0 hT1).intervalIntegrable x a b)).symm
  · have hc : Continuous (fun t => compactGradient W γ T t x) :=
      (compactGradient_continuous W γ hT0 hT1).comp
        (continuous_id.prodMk continuous_const)
    exact (hc.mul hc).continuousOn
  · intro t ht
    have hd := compactGradient_hasDerivWithinAt_right W γ hT0 hT1 (ha.trans ht.1.le) (ht.2.trans_le hb) x
    convert hd.mul hd using 1 <;> (try rfl)
    dsimp only [compactSquareRate]
    ring

lemma compactSquare_generator (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactSquare W γ T t) x*compactDrift W γ T t x+
      (1/2:ℝ)*deriv (deriv (compactSquare W γ T t)) x+compactSquareRate W γ T t x =
      (deriv (compactGradient W γ T t) x)^2 := by
  have hu := compactGradient_family W γ hT0 hT1
  have hd (x : ℝ) := ((hu.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hdd (x : ℝ) := ((hu.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he (x : ℝ) : deriv (compactSquare W γ T t) x =
      deriv (compactGradient W γ T t) x*compactGradient W γ T t x+
        compactGradient W γ T t x*deriv (compactGradient W γ T t) x := (hd x |>.mul (hd x)).deriv
  have he2 : deriv (compactSquare W γ T t) = fun x =>
      deriv (compactGradient W γ T t) x*compactGradient W γ T t x+
        compactGradient W γ T t x*deriv (compactGradient W γ T t) x := funext he
  have hh := ((hdd x |>.mul (hd x)).add ((hd x).mul (hdd x))).deriv
  change deriv (fun y => deriv (compactGradient W γ T t) y*compactGradient W γ T t y+
    compactGradient W γ T t y*deriv (compactGradient W γ T t) y) x = _ at hh
  rw [he,he2,hh]
  unfold compactDrift compactSquareRate
  rw [deriv_compactValueRate W γ hT0 hT1]
  ring

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma BoundedLipschitzDrift.expected_continuous (b : BoundedLipschitzDrift)
    (W : BrownianSystem Ω) {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun r : ℝ => ∫ ω, F r (b.solution W.driver (Real.toNNReal r) ω) ∂W.law) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := hF.bound
  apply continuous_of_dominated (bound := fun _ => (C:ℝ))
  · intro r
    exact ((hF.regular r).smooth.continuous.measurable.comp
      (b.solution_measurable W (Real.toNNReal r))).aestronglyMeasurable
  · intro r
    exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC r (b.solution W.driver (Real.toNNReal r) ω))
  · exact integrable_const _
  · filter_upwards [b.solution_continuous_ae W] with ω hω
    exact hc.comp (continuous_id.prodMk (hω.comp (by fun_prop : Continuous Real.toNNReal)))

lemma stripDrift_pathDrift_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) :
    ∀ᵐ ω ∂W.law, ContinuousWithinAt (fun r => (stripDrift W γ T).pathDrift W r ω) (Ioi (s:ℝ)) s := by
  filter_upwards [(stripDrift W γ T).solution_continuous_ae W] with ω hω
  have hx : Continuous (fun r : ℝ => (stripDrift W γ T).solution W.driver (Real.toNNReal r) ω) :=
    hω.comp (by fun_prop : Continuous Real.toNNReal)
  have hu : Continuous (fun r : ℝ => compactGradient W γ T r
      ((stripDrift W γ T).solution W.driver (Real.toNNReal r) ω)) :=
    (compactGradient_continuous W γ T.property.1 T.property.2).comp (continuous_id.prodMk hx)
  have hh := ((compactCoeff_rightContinuous γ T.property.1 T.property.2 (s:ℝ)).mono Ioi_subset_Ici_self).mul hu.continuousWithinAt
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [BoundedLipschitzDrift.pathDrift,stripDrift,compactDrift,
      Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le),Pi.mul_apply]
  · simp only [BoundedLipschitzDrift.pathDrift,stripDrift,compactDrift,Real.toNNReal_coe,Pi.mul_apply]

lemma compactSquare_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactSquare W γ T p.1 p.2) :=
  (compactGradient_continuous W γ hT0 hT1).mul (compactGradient_continuous W γ hT0 hT1)

lemma compactCurvatureSquare_continuous (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => (deriv (compactGradient W γ T p.1) p.2)^2) := by
  have hh := compactGradient_derivative_continuous W γ hT0 hT1 1
  simp only [iteratedDeriv_one] at hh
  exact hh.pow 2

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.StripSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma stripQ_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Continuous (stripQ W γ T) :=
  (stripDrift W γ T).expected_continuous W (compactSquare_family W γ T.property.1 T.property.2)
    (compactSquare_continuous W γ T.property.1 T.property.2)

lemma stripA_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Continuous (stripA W γ T) := by
  have hu := (compactGradient_family W γ T.property.1 T.property.2).deriv
  have hf : BoundedSmoothFamily (fun t x => (deriv (compactGradient W γ T t) x)^2) := by
    simpa only [pow_two] using hu.mul hu
  exact (stripDrift W γ T).expected_continuous W hf
    (compactCurvatureSquare_continuous W γ T.property.1 T.property.2)

lemma stripQ_zero (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) : stripQ W γ T 0 = 0 := by
  have hx (ω : Ω) : (stripDrift W γ T).solution W.driver 0 ω = 0 := by
    rw [(stripDrift W γ T).solution_eq _ W.driver_progressive]
    simp only [NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]
  have hu : compactGradient W γ T 0 0 = 0 := by
    rw [compactGradient,stripClamp_eq ⟨le_rfl,T.property.1⟩]
    exact gradient_zero W γ (by norm_num) (by norm_num)
  simp only [stripQ,Real.toNNReal_zero,hx,compactSquare,hu,mul_zero,integral_zero]

lemma stripQ_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) (hsT : (s:ℝ) < T) :
    HasDerivWithinAt (stripQ W γ T) (stripA W γ T s) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  let b := stripDrift W γ T
  have hf := compactSquare_family W γ T.property.1 T.property.2
  have hd := compactSquareRate_family W γ T.property.1 T.property.2
  have hgen := expected_hasDerivWithinAt_right W b hf hd
    (fun a c ha hac hc => compactSquare_integral_rate W γ T.property.1 T.property.2 ha hac hc)
    s hsT (compactSquareRate_right W γ T.property.1 T.property.2 (s:ℝ)) (stripDrift_pathDrift_right W γ T s)
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ω => deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω) W.law := by
    apply (integrable_family_comp hf.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => b.pathDrift_bound W s ω)
  have hi2 := integrable_family_comp (P := W.law) hf.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) hd (s:ℝ) hx
  have he : (∫ ω, deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω ∂W.law)+
      (1/2:ℝ)*(∫ ω, deriv (deriv (compactSquare W γ T s)) (b.solution W.driver s ω) ∂W.law)+
      (∫ ω, compactSquareRate W γ T s (b.solution W.driver s ω) ∂W.law) = stripA W γ T s := by
    have hi12 : Integrable (fun ω => deriv (compactSquare W γ T s) (b.solution W.driver s ω)*b.pathDrift W s ω+
        (1/2:ℝ)*deriv (deriv (compactSquare W γ T s)) (b.solution W.driver s ω)) W.law :=
      hi1.add (hi2.const_mul (1/2:ℝ))
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),← integral_add hi12 hi3]
    apply integral_congr_ae
    filter_upwards [] with ω
    simpa only [stripA,Real.toNNReal_coe,BoundedLipschitzDrift.pathDrift,b,stripDrift] using
      compactSquare_generator W γ T.property.1 T.property.2 (s:ℝ) (b.solution W.driver s ω)
  rw [he] at hgen
  exact hgen

theorem stripQ_eq_integral (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    stripQ W γ T t = ∫ s in (0:ℝ)..t, stripA W γ T s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht0
    (stripQ_continuous W γ T).continuousOn
    (fun s hs => by
      have hh := stripQ_hasDerivWithinAt_right W γ T (Real.toNNReal s)
        (by rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2.trans_le htT)
      simpa only [Real.coe_toNNReal _ hs.1.le] using hh)
    ((stripA_continuous W γ T).intervalIntegrable 0 t)
  rw [stripQ_zero,sub_zero] at hi
  exact hi.symm

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma diffusion_eq_strip (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (s : ℝ≥0) (hs : (s:ℝ) ≤ T) (ω : Ω) :
    diffusion W γ s ω = (stripDrift W γ T).solution W.driver s ω := by
  have hs1 := hs.trans_lt T.property.2
  obtain ⟨n,hn⟩ := (eventually_le_diffusionHorizon hs1).exists
  rw [diffusion_eq_raw W γ s hs1,rawDiffusion_eq_local W γ n s hn]
  apply (stripDrift W γ (diffusionHorizonTime n)).solution_eq_of_agree
    (stripDrift W γ T) _ W.driver_progressive s _ s le_rfl ω
  intro r hr x
  have hrs : (r:ℝ) ≤ (s:ℝ) := hr
  rw [stripDrift_eq W γ _ ⟨r.coe_nonneg,hrs.trans hn⟩,
    stripDrift_eq W γ _ ⟨r.coe_nonneg,hrs.trans hs⟩]

lemma stripQ_eq_squareMoment (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripQ W γ T t = squareMoment W γ (diffusion W γ) t := by
  have hs : ((Real.toNNReal t):ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  unfold stripQ squareMoment
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [diffusion_eq_strip W γ T _ hs]
  simp only [compactSquare,compactGradient,stripClamp_eq ht,pow_two]

lemma stripA_eq_curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : stripA W γ T t = curvatureMoment W γ t := by
  have hs : ((Real.toNNReal t):ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  have he : compactGradient W γ T t = gradient W γ t := by
    funext x
    simp only [compactGradient,stripClamp_eq ht]
  unfold stripA curvatureMoment
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [diffusion_eq_strip W γ T _ hs,he]
  rfl

theorem squareMoment_eq_integral_curvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    squareMoment W γ (diffusion W γ) t = ∫ s in (0:ℝ)..t, curvatureMoment W γ s := by
  let T : Time := ⟨t,⟨ht0,ht1⟩⟩
  rw [← stripQ_eq_squareMoment W γ T ⟨ht0,le_rfl⟩,stripQ_eq_integral W γ T ht0 le_rfl]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht0] at hs
  exact stripA_eq_curvatureMoment W γ T hs

lemma curvatureMoment_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : ContinuousOn (curvatureMoment W γ) (Icc (0:ℝ) T) := by
  exact (stripA_continuous W γ ⟨T,⟨hT0,hT1⟩⟩).continuousOn.congr
    (fun t ht => (stripA_eq_curvatureMoment W γ ⟨T,⟨hT0,hT1⟩⟩ ht).symm)

lemma squareMoment_zero (W : BrownianSystem Ω) (γ : OrderParameter) :
    squareMoment W γ (diffusion W γ) 0 = 0 := by
  rw [squareMoment_eq_integral_curvatureMoment W γ (by norm_num) (by norm_num),intervalIntegral.integral_same]

theorem squareMoment_hasDerivWithinAt (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivWithinAt (squareMoment W γ (diffusion W γ)) (curvatureMoment W γ t) (Ici (0:ℝ)) t := by
  let T : Time := ⟨(t+1)/2,⟨by linarith,by linarith⟩⟩
  have htt : t < (T:ℝ) := by dsimp [T]; linarith
  have hc := stripA_continuous W γ T
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [stripA_eq_curvatureMoment W γ T ⟨ht0,htt.le⟩] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htt)] with s hs hsT
    rw [← stripQ_eq_squareMoment W γ T ⟨hs,hsT.le⟩,stripQ_eq_integral W γ T hs hsT.le]
  · rw [← stripQ_eq_squareMoment W γ T ⟨ht0,htt.le⟩,stripQ_eq_integral W γ T ht0 htt.le]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.TerminalTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma value_regular (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : RegularDatum (value W γ t) := by
  refine ⟨value_contDiff W γ ht0 ht1,?_⟩
  have hh := (compactGradient_family W γ ht0 ht1).regular t
  change BoundedSmooth (deriv (value W γ (stripClamp t t))) at hh
  rw [stripClamp_eq (show t ∈ Icc (0:ℝ) t from ⟨ht0,le_rfl⟩)] at hh
  exact hh

lemma gradientDefect_smooth (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : BoundedSmooth (fun x => 1-(gradient W γ t x)^2) := by
  have hu := (value_regular W γ ht0 ht1).deriv_bounded
  convert (BoundedSmooth.const 1).add ((hu.mul hu).const_mul (-1)) using 1 <;> try rfl
  funext x
  unfold gradient
  ring

theorem terminal_plateau_transition (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s T : Time) (has : a < (s:ℝ)) (hsT : s ≤ T) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    (∫ ξ, g (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ) ∂W.law)=
      ∫ ξ, varianceTilted c ((T:ℝ)-s) (value W γ T) g
        (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ) ∂W.law := by
  have hm : ∀ t ∈ Ico (s:ℝ) T, ∀ x,
      (stripDrift W γ T).f t x=c*deriv (varianceLogHeat c ((T:ℝ)-t) (value W γ T)) x := by
    intro t ht x
    rw [stripDrift_eq W γ T ⟨s.property.1.trans ht.1,ht.2.le⟩,
      hc t ⟨has.trans_le ht.1,ht.2.trans T.property.2⟩]
    unfold gradient
    rw [value_plateau_semigroup W γ hc0 (s.property.1.trans ht.1) (has.trans_le ht.1) ht.2.le T.property.2 hc]
  have hh := expected_transition_tiltedMean W (stripDrift W γ T)
    (value_regular W γ T.property.1 T.property.2) (value_lipschitz W γ T T.property.2.le) hg hc0
    (a := (⟨s,s.property.1⟩:ℝ≥0)) (T := (⟨T,T.property.1⟩:ℝ≥0)) hsT hm
  have eT : diffusion W γ (⟨T,T.property.1⟩:ℝ≥0)=(stripDrift W γ T).solution W.driver (⟨T,T.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ T (⟨T,T.property.1⟩:ℝ≥0) le_rfl)
  have es : diffusion W γ (⟨s,s.property.1⟩:ℝ≥0)=(stripDrift W γ T).solution W.driver (⟨s,s.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ T (⟨s,s.property.1⟩:ℝ≥0) hsT)
  rw [eT,es]
  exact hh

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.DensityHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma heatKernel_formula {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    heatKernel t x=(Real.sqrt (2*Real.pi*t))⁻¹*Real.exp (-x^2/(2*t)) := by
  simp only [heatKernel,gaussianPDFReal,Real.coe_toNNReal _ ht,sub_zero]

lemma heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x :=
  gaussianPDFReal_pos 0 _ x (ne_of_gt (Real.toNNReal_pos.mpr ht))

lemma varianceHeat_kernel {g : ℝ → ℝ} (hg : Measurable g) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    varianceHeat t g x=∫ y, heatKernel t (y-x)*g y := by
  rw [varianceHeat_eq_semigroup_toNNReal hg]
  unfold semigroup
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr ht))]
  rw [← integral_add_left_eq_self (fun y => heatKernel t (y-x)*g y) x]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [heatKernel,smul_eq_mul,add_sub_cancel_left]

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma heatKernel_uniform_lower {δ h x y : ℝ} (hδ : 0 < δ) (hδh : δ ≤ h) (hh : h ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ) ≤ heatKernel h (y-x) := by
  have hh0 := hδ.trans_le hδh
  have hz : |y-x| ≤ 2 := (abs_sub y x).trans (by linarith)
  have hz2 : (y-x)^2 ≤ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (y-x)) (show (0:ℝ) ≤ 2 by norm_num)).mpr hz
    simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using hh
  rw [heatKernel_formula hh0.le]
  apply mul_le_mul
  · apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  · apply Real.exp_le_exp.mpr
    have hq : (y-x)^2/(2*h) ≤ 2/δ := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*h) hδ).mpr
      nlinarith
    simpa only [neg_div] using neg_le_neg hq
  · positivity
  · positivity

lemma integrable_weighted_heatKernel {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y => heatKernel h (y-x)*(g y*Real.exp (c*f y))) := by
  obtain ⟨G,hG⟩ := hg.bound
  have hi := integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c (Real.toNNReal h) x
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt (Real.toNNReal_pos.mpr hh))] at hi
  have hj := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 (Real.toNNReal h))
    (Eventually.of_forall (fun y => gaussianPDF_lt_top))).mp hi
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] at hj
  have hk := hj.comp_add_left (-x)
  apply hk.congr
  filter_upwards [] with y
  simp only [← add_assoc,add_neg_cancel,zero_add]
  rw [show -x+y=y-x by ring]
  rfl

lemma varianceHeat_exp_eq_exp_log {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c h x : ℝ) : varianceHeat h (fun y => Real.exp (c*f y)) x=Real.exp (c*varianceLogHeat c h f x) := by
  by_cases hc : c=0
  · subst c
    simp only [zero_mul,Real.exp_zero]
    unfold varianceHeat scaled
    simp
  · unfold varianceLogHeat
    rw [ite_eq_right hc]
    rw [mul_div_cancel₀ _ hc,Real.exp_log (varianceHeat_exp_pos hf c h x)]

lemma varianceTilted_lower_window {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) {c δ h r x M : ℝ}
    (hc : 0 ≤ c) (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hδ : 0 < δ) (hδh : δ ≤ h) (hh1 : h ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : |x| ≤ 1) (hgwin : ∀ y, |y| ≤ r → 3/4 ≤ g y)
    (hden : varianceHeat h (fun y => Real.exp (c*f y)) x ≤ M) :
    ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r)/M ≤ varianceTilted c h f g x := by
  have hh0 := hδ.trans_le hδh
  have hM : 0 < M := (varianceHeat_exp_pos hf c h x).trans_le hden
  let k : ℝ := (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)
  have hk : 0 ≤ k := by dsimp [k];positivity
  have hi := integrable_weighted_heatKernel hf hg c hh0 x
  have hnon (y : ℝ) : 0 ≤ heatKernel h (y-x)*(g y*Real.exp (c*f y)) :=
    mul_nonneg (heatKernel_pos hh0 _).le (mul_nonneg (hg0 y) (Real.exp_nonneg _))
  have hlower : (3/4:ℝ)*k*(2*r) ≤ ∫ y, heatKernel h (y-x)*(g y*Real.exp (c*f y)) := by
    have hm := setIntegral_mono_on (f := fun _ => (3/4:ℝ)*k)
      (s := Icc (-r) r) (integrableOn_const measure_Icc_lt_top.ne) hi.integrableOn measurableSet_Icc
      (fun y hy => by
        have hab : |y| ≤ r := abs_le.mpr hy
        have hw := heatKernel_uniform_lower hδ hδh hh1 hx (hab.trans hr1)
        have hg' := hgwin y hab
        have hex : 1 ≤ Real.exp (c*f y) := Real.one_le_exp_iff.mpr (mul_nonneg hc (hf0 y))
        have hge : (3/4:ℝ) ≤ g y*Real.exp (c*f y) := le_trans hg' (by nlinarith [hg0 y])
        change (3/4:ℝ)*k ≤ _
        rw [mul_comm (3/4:ℝ)]
        exact mul_le_mul hw hge (by norm_num) (heatKernel_pos hh0 _).le)
    have hs : ∫ _y in Icc (-r) r, (3/4:ℝ)*k = (3/4:ℝ)*k*(2*r) := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (neg_le_self hr0),smul_eq_mul]
      ring
    rw [hs] at hm
    exact hm.trans (setIntegral_le_integral hi (Eventually.of_forall hnon))
  have hgm := hg.smooth.continuous.measurable
  have hfm := hf.continuous.measurable
  unfold varianceTilted
  rw [varianceHeat_kernel (g := fun y => g y*Real.exp (c*f y)) (by fun_prop) hh0]
  have hn : 0 ≤ (3/4:ℝ)*k*(2*r) := by positivity
  have hd := div_le_div_of_nonneg_left hn (varianceHeat_exp_pos hf c h x) hden
  have hu := div_le_div_of_nonneg_right hlower (varianceHeat_exp_pos hf c h x).le
  have he : (3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r=(3/4:ℝ)*k*(2*r) := by dsimp [k];ring
  rw [he]
  exact hd.trans hu

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.Diffusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma independent_gaussian_sum_interval_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z) {v : ℝ≥0} (hv : v ≠ 0)
    (hLaw : HasLaw Z (gaussianReal 0 v) P) (hi : IndepFun Y Z P)
    {a b : ℝ} (hab : a < b) : 0 < P {ξ | Y ξ+Z ξ ∈ Ioo a b} := by
  let S : Set (ℝ × ℝ) := {p | p.1+p.2 ∈ Ioo a b}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (measurable_fst.add measurable_snd)
  have he := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hi
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp : ((P.map Y).prod (gaussianReal 0 v)) S=0 := by
    rw [← hLaw.map_eq,← he,Measure.map_apply (hY.prodMk hZ) hS]
    exact hz
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  obtain ⟨y,hy⟩ := (Measure.measure_prod_null hS |>.mp hp).exists
  have hy0 := gaussianReal_absolutelyContinuous' 0 hv hy
  have hsec : Prod.mk y ⁻¹' S=Ioo (a-y) (b-y) := by
    ext z
    change (a < y+z ∧ y+z < b) ↔ (a-y < z ∧ z < b-y)
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hsec,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hy0
  linarith

lemma BoundedLipschitzDrift.solution_interval_pos (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (t : ℝ≥0) (ht : 0 < (t:ℝ)) {a c : ℝ} (hac : a < c) :
    0 < W.law {ξ | b.solution W.driver t ξ ∈ Ioo a c} := by
  let := W.isProbability
  have hD : 0 < (b.bound:ℝ)+1 := by positivity
  have hw : 0 < (c-a)/(4*((b.bound:ℝ)+1)) := div_pos (sub_pos.mpr hac) (by positivity)
  obtain ⟨h,hh0,hh⟩ := exists_between (lt_min ht hw)
  have hht : h < (t:ℝ) := (lt_min_iff.mp hh).1
  have hhw : 4*((b.bound:ℝ)+1)*h < c-a := by
    have h1 := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*((b.bound:ℝ)+1))).mp (lt_min_iff.mp hh).2
    nlinarith
  have hdh : 2*(b.bound:ℝ)*h < c-a := by nlinarith [b.bound.coe_nonneg]
  let H : ℝ≥0 := ⟨h,hh0.le⟩
  let S : ℝ≥0 := ⟨(t:ℝ)-h,sub_nonneg.mpr hht.le⟩
  have htime : S+H=t := by apply NNReal.coe_injective;change (t:ℝ)-h+h=t;ring
  have hi := adapted_indep_increment W.brownian.toIsPreBrownianReal W.measurable S H (b.solution_adapted W S)
  have hLaw := W.brownian.toIsPreBrownianReal.hasLaw_sub (S+H) S
  have hv : nndist ((S+H:ℝ≥0):ℝ) (S:ℝ)=H := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg H.coe_nonneg]
  have hLaw' : HasLaw (fun ξ => W.B (S+H) ξ-W.B S ξ) (gaussianReal 0 H) W.law := by
    convert hLaw using 1 <;> try rfl
    congr 1
    exact hv.symm
  have hp := independent_gaussian_sum_interval_pos W.law (b.solution_measurable W S)
    ((W.measurable (S+H)).sub (W.measurable S)) (show H ≠ 0 from ne_of_gt hh0) hLaw' hi
    (a := a+(b.bound:ℝ)*h) (b := c-(b.bound:ℝ)*h) (by linarith)
  apply hp.trans_le
  apply measure_mono_ae
  filter_upwards [b.solution_increment W S H] with ξ hξ hmem
  rw [htime,← NNReal.coe_add,htime] at hξ
  have hd := b.displacement_bound W S t ξ
  have he : |(t:ℝ)-(S:ℝ)|=h := by change |(t:ℝ)-((t:ℝ)-h)|=h; rw [sub_sub_cancel,abs_of_pos hh0]
  rw [he] at hd
  rcases abs_le.mp hd with ⟨hdl,hdu⟩
  change a+(b.bound:ℝ)*h < b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) ∧
    b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) < c-(b.bound:ℝ)*h at hmem
  rw [htime] at hmem
  change a < b.solution W.driver t ξ ∧ b.solution W.driver t ξ < c
  rw [hξ]
  constructor <;> linarith [hmem.1,hmem.2]

theorem diffusion_interval_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) {a b : ℝ} (hab : a < b) :
    0 < W.law {ξ | diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ ∈ Ioo a b} := by
  have he : diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)=(stripDrift W γ t).solution W.driver (⟨t,t.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ t _ le_rfl)
  rw [he]
  exact (stripDrift W γ t).solution_interval_pos W (⟨t,t.property.1⟩:ℝ≥0) ht hab

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.TimeFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto

namespace TimeField
variable {T : ℝ}

lemma integral_rate (F : TimeField T) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
    F.f b x-F.f a x=∫ t in a..b, F.d t x := by
  apply (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab _ _
    (F.rate_smooth.intervalIntegrable x a b)).symm
  · exact (F.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · intro t ht
    exact F.time_deriv t (ha.trans ht.1.le) (ht.2.trans_le hb) x

lemma generator_mul (F G : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.mul G).generator b t x=F.f t x*G.generator b t x+G.f t x*F.generator b t x+
      deriv (F.f t) x*deriv (G.f t) x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hG (x : ℝ) := ((G.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hGd (x : ℝ) := ((G.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => F.f t y*G.f t y)=fun y => deriv (F.f t) y*G.f t y+F.f t y*deriv (G.f t) y :=
    funext (fun y => ((hF y).mul (hG y)).deriv)
  have hd := (((hFd x).mul (hG x)).add ((hF x).mul (hGd x))).deriv
  change deriv (fun y => deriv (F.f t) y*G.f t y+F.f t y*deriv (G.f t) y) x = _ at hd
  dsimp only [generator,mul]
  rw [he,hd]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma expected_continuous (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) :
    Continuous (F.expected b W) := by
  let := W.isProbability
  obtain ⟨bound,hbound⟩ := F.smooth.bound
  apply continuous_of_dominated (bound := fun _ => (bound:ℝ))
  · intro time
    exact (integrable_family_comp F.smooth time (b.solution_measurable W _)).aestronglyMeasurable
  · intro time
    exact Eventually.of_forall (fun sample => by
      simpa only [Real.norm_eq_abs] using
        hbound time (b.solution W.driver (Real.toNNReal time) sample))
  · exact integrable_const _
  · filter_upwards [b.solution_continuous_ae W] with sample hsample
    exact F.continuous.comp (continuous_id.prodMk (hsample.comp continuous_real_toNNReal))

lemma expected_hasDerivWithinAt_right (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (s : ℝ≥0) (hs : (s:ℝ) < T)
    (hbr : ∀ᵐ ξ ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r ξ) (Ioi (s:ℝ)) s) :
    HasDerivWithinAt (F.expected b W)
      (∫ ξ, F.generator b.f s (b.solution W.driver s ξ) ∂W.law) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  have hd := ZeroTemperatureSK.expected_hasDerivWithinAt_right W b F.smooth F.rate_smooth
    (fun a c ha hac hc x => F.integral_rate ha hac hc x) s hs (F.rate_right s) hbr
  have hx := b.solution_measurable W s
  have hi1 : Integrable (fun ξ => deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ) W.law := by
    apply (integrable_family_comp F.smooth.deriv (s:ℝ) hx).mul_bdd
    · exact ((b.pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    · exact Eventually.of_forall (fun ξ => b.pathDrift_bound W s ξ)
  have hi2 := integrable_family_comp (P := W.law) F.smooth.deriv.deriv (s:ℝ) hx
  have hi3 := integrable_family_comp (P := W.law) F.rate_smooth (s:ℝ) hx
  have he : (∫ ξ, deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ ∂W.law)+
      (1/2:ℝ)*(∫ ξ, deriv (deriv (F.f s)) (b.solution W.driver s ξ) ∂W.law)+
      (∫ ξ, F.d s (b.solution W.driver s ξ) ∂W.law) =
        ∫ ξ, F.generator b.f s (b.solution W.driver s ξ) ∂W.law := by
    have hi12 : Integrable (fun ξ => deriv (F.f s) (b.solution W.driver s ξ)*b.pathDrift W s ξ+
        (1/2:ℝ)*deriv (deriv (F.f s)) (b.solution W.driver s ξ)) W.law := hi1.add (hi2.const_mul (1/2:ℝ))
    rw [← integral_const_mul,← integral_add hi1 (hi2.const_mul (1/2:ℝ)),
      ← integral_add hi12 hi3]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [generator,BoundedLipschitzDrift.pathDrift,Real.toNNReal_coe]
  rw [he] at hd
  exact hd

end TimeField
end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.ParameterChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma OrderParameter.chord_extend (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) (t : ℝ) :
    extend (γ.chord β ε hε).val t=extend γ.val t+ε*(extend β.val t-extend γ.val t) := by
  by_cases ht : t ∈ Ico (0:ℝ) 1
  · simp only [extend,dite_eq_left ht,chord];ring
  · simp [extend,ht]

lemma OrderParameter.chord_distance (γ β : OrderParameter) (ε : ℝ) (hε : ε ∈ Icc (0:ℝ) 1) :
    coefficientDistance (γ.chord β ε hε) γ=ε*coefficientDistance β γ := by
  simp only [coefficientDistance,γ.chord_extend β ε hε,add_sub_cancel_left,abs_mul,abs_of_nonneg hε.1]
  rw [intervalIntegral.integral_const_mul]

lemma variationStep_limit : Tendsto variationStep atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)
  simpa only [variationStep,one_div,Function.comp_def,Nat.cast_add,Nat.cast_one] using tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

lemma perturbation_diff (γ β : OrderParameter) (n : ℕ) (t : ℝ) :
    extend (perturbation γ β n).val t-extend γ.val t=variationStep n*(extend β.val t-extend γ.val t) := by
  simp only [perturbation,γ.chord_extend β _ _,add_sub_cancel_left]

lemma perturbation_distance_limit (γ β : OrderParameter) :
    Tendsto (fun n => coefficientDistance (perturbation γ β n) γ) atTop (𝓝 0) := by
  simp only [perturbation,OrderParameter.chord_distance]
  simpa only [zero_mul] using variationStep_limit.mul_const (coefficientDistance β γ)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.DiffusionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma solution_stability_on (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {E : ℝ} (hE : 0 ≤ E)
    (ω : Ω)
    (he : ∀ t ≤ T, |timePrimitive (b.action B (b'.correction B)) t ω-b'.correction B t ω| ≤ E)
    (t : ℝ≥0) (ht : t ≤ T) :
    |b.solution B t ω-b'.solution B t ω| ≤ 2*E*Real.exp (b.rate*t) := by
  let A : ℝ := ((b.bound:ℝ)+(b'.bound:ℝ))*(T:ℝ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hbase (s : ℝ≥0) (hs : s ≤ T) : |b.correction B s ω-b'.correction B s ω| ≤ A := by
    apply (abs_sub _ _).trans
    have hb := b.correction_bound ℱ hB s ω
    have hb' := b'.correction_bound ℱ hB s ω
    have hst : (s:ℝ) ≤ T := hs
    dsimp [A]
    nlinarith [b.bound.coe_nonneg,b'.bound.coe_nonneg]
  have hest (n : ℕ) (s : ℝ≥0) (hs : s ≤ T) :
      |b.correction B s ω-b'.correction B s ω| ≤ (2*E+A*(1/2:ℝ)^n)*Real.exp (b.rate*s) := by
    induction n generalizing s with
    | zero =>
      simp only [pow_zero,mul_one]
      apply (hbase s hs).trans
      have hex : 1 ≤ Real.exp (b.rate*s) := Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      nlinarith
    | succ n ih =>
      have hh := b.timePrimitive_action_sub_estimate ℱ hB (b.correction_progressive ℱ hB)
        (b'.correction_progressive ℱ hB) (show 0 ≤ 2*E+A*(1/2:ℝ)^n by positivity)
        s ω (fun u hu => ih u (hu.trans hs))
      rw [← b.correction_eq_integral ℱ hB] at hh
      have htri := abs_sub_le (b.correction B s ω)
        (timePrimitive (b.action B (b'.correction B)) s ω) (b'.correction B s ω)
      have her := he s hs
      have hex : 1 ≤ Real.exp (b.rate*s) := Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hex hE]
  have hlim : Tendsto (fun n : ℕ => (2*E+A*(1/2:ℝ)^n)*Real.exp (b.rate*t)) atTop
      (𝓝 (2*E*Real.exp (b.rate*t))) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds.add (tendsto_const_nhds.mul hh) (a := 2*E)).mul_const (Real.exp (b.rate*t))
  have hh := ge_of_tendsto hlim (Eventually.of_forall (fun n => hest n t ht))
  simpa only [solution,add_sub_add_left_eq_sub] using hh

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma residual_integral_bound (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {e : ℝ → ℝ}
    (hei : IntervalIntegrable e volume 0 T)
    (hen : ∀ s ∈ Icc (0:ℝ) T, 0 ≤ e s)
    (he : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x, |b.f s x-b'.f s x| ≤ e s)
    (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    |timePrimitive (b.action B (b'.correction B)) t ω-b'.correction B t ω| ≤ ∫ s in (0:ℝ)..(T:ℝ), e s := by
  have hZ := b'.correction_progressive ℱ hB
  have hi := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hZ) (b.action_bound _ _) ω 0 t
  have hi' := progressive_bounded_integrable ℱ (b'.action_progressive ℱ hB hZ) (b'.action_bound _ _) ω 0 t
  rw [b'.correction_eq_integral ℱ hB,timePrimitive,timePrimitive,← intervalIntegral.integral_sub hi hi']
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ), e s := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
        (hei.mono_set (by rw [uIcc_of_le t.coe_nonneg,uIcc_of_le T.coe_nonneg];exact Icc_subset_Icc le_rfl ht))
      filter_upwards [he] with s hs hst
      have hmem : s ∈ Icc (0:ℝ) T := ⟨hst.1.le,hst.2.trans ht⟩
      change |b.f (Real.toNNReal s) _-b'.f (Real.toNNReal s) _| ≤ e s
      rw [Real.coe_toNNReal _ hmem.1]
      exact hs hmem _
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg ht _ hei
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hen s ⟨hs.1.le,hs.2⟩

lemma solution_stability_integral (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {e : ℝ → ℝ}
    (hei : IntervalIntegrable e volume 0 T)
    (hen : ∀ s ∈ Icc (0:ℝ) T, 0 ≤ e s)
    (he : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x, |b.f s x-b'.f s x| ≤ e s)
    (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    |b.solution B t ω-b'.solution B t ω| ≤
      2*(∫ s in (0:ℝ)..(T:ℝ), e s)*Real.exp (b.rate*t) := by
  exact solution_stability_on b b' ℱ hB T
    (intervalIntegral.integral_nonneg T.coe_nonneg (fun s hs => hen s hs)) ω
    (fun u hu => residual_integral_bound b b' ℱ hB T hei hen he u hu ω) t ht

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma mul_sub_mul_error {a b u v D δ : ℝ} (hδ : 0 ≤ δ) (hD : |a| ≤ D)
    (hv : |v| ≤ 1) (huv : |u-v| ≤ δ) : |a*u-b*v| ≤ |a-b|+D*δ := by
  calc
    _ = |(a-b)*v+a*(u-v)| := by congr 1;ring
    _ ≤ |(a-b)*v|+|a*(u-v)| := abs_add_le _ _
    _ = |a-b| * |v|+|a| * |u-v| := by rw [abs_mul,abs_mul]
    _ ≤ |a-b| * 1+D*δ := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
      ((mul_le_mul_of_nonneg_left huv (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hD hδ))
    _ = _ := by ring

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.MixedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma mixedStripDrift_pathDrift_right (W : BrownianSystem Ω) (β γ : OrderParameter)
    (T : Time) (s : ℝ≥0) :
    ∀ᵐ ξ ∂W.law, ContinuousWithinAt (fun r => (mixedStripDrift W β γ T).pathDrift W r ξ) (Ioi (s:ℝ)) s := by
  filter_upwards [(mixedStripDrift W β γ T).solution_continuous_ae W] with ξ hξ
  have hx : Continuous (fun r : ℝ => (mixedStripDrift W β γ T).solution W.driver (Real.toNNReal r) ξ) :=
    hξ.comp (by fun_prop : Continuous Real.toNNReal)
  have hu : Continuous (fun r : ℝ => compactMixedGradient W β γ T r
      ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal r) ξ)) :=
    (compactMixedGradient_continuous W β γ T.property.1 T.property.2).comp (continuous_id.prodMk hx)
  have hh := ((compactCoeff_rightContinuous β T.property.1 T.property.2 (s:ℝ)).mono Ioi_subset_Ici_self).mul hu.continuousWithinAt
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [BoundedLipschitzDrift.pathDrift,mixedStripDrift,compactMixedDrift,
      Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le),Pi.mul_apply]
  · simp only [BoundedLipschitzDrift.pathDrift,mixedStripDrift,compactMixedDrift,Real.toNNReal_coe,Pi.mul_apply]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.MixedPathStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma mixedDrift_error (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s x, |compactGradient W β T s x-compactGradient W γ T s x| ≤ δ) :
    ∀ s ∈ Icc (0:ℝ) T, ∀ x,
      |(stripDrift W γ T).f s x-(mixedStripDrift W β γ T).f s x| ≤
        |extend β.val s-extend γ.val s|+γ.val T*δ := by
  intro s hs x
  have hm : |compactGradient W γ T s x-compactMixedGradient W β γ T s x| ≤ δ := by
    have he : compactGradient W γ T s x-compactMixedGradient W β γ T s x=
        -(compactGradient W β T s x-compactGradient W γ T s x)/2 := by unfold compactMixedGradient;ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hh := hd s x
    linarith
  have hc : |compactCoeff γ T s| ≤ γ.val T := by
    rw [abs_of_nonneg (compactCoeff_bounds γ T.property.1 T.property.2 s).1]
    exact (compactCoeff_bounds γ T.property.1 T.property.2 s).2
  have hh := mul_sub_mul_error (b := compactCoeff β T s) hδ hc
    (compactMixedGradient_bound W β γ T.property.1 T.property.2 s x) hm
  simpa only [stripDrift,compactDrift,mixedStripDrift,compactMixedDrift,compactCoeff,stripClamp_eq hs,abs_sub_comm] using hh

lemma mixedPath_error (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s x, |compactGradient W β T s x-compactGradient W γ T s x| ≤ δ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |(mixedStripDrift W β γ T).solution W.driver t ξ-diffusion W γ t ξ| ≤
      2*(coefficientDistance β γ+γ.val T*(T:ℝ)*δ)*Real.exp ((stripDrift W γ T).rate*T) := by
  let e (s : ℝ) := |extend β.val s-extend γ.val s|+γ.val T*δ
  have hei (a b : ℝ) : IntervalIntegrable e volume a b :=
    ((β.integrable.sub γ.integrable).abs.intervalIntegrable).add intervalIntegrable_const
  have hen (s : ℝ) : 0 ≤ e s := add_nonneg (abs_nonneg _) (mul_nonneg (γ.nonneg _) hδ)
  let TT : ℝ≥0 := ⟨T,T.property.1⟩
  have hh := (stripDrift W γ T).solution_stability_integral (mixedStripDrift W β γ T) _ W.driver_progressive TT
    (hei 0 T) (fun s _ => hen s) (Eventually.of_forall (fun s => mixedDrift_error W β γ T hδ hd s)) t ht ξ
  rw [← diffusion_eq_strip W γ T t ht,abs_sub_comm] at hh
  have hi0 : 0 ≤ ∫ s in (0:ℝ)..(T:ℝ), e s := intervalIntegral.integral_nonneg T.property.1 (fun s _ => hen s)
  have hi : (∫ s in (0:ℝ)..(T:ℝ), e s) ≤ coefficientDistance β γ+γ.val T*(T:ℝ)*δ := by
    dsimp only [e,coefficientDistance]
    have hfi : IntervalIntegrable (fun s => |extend β.val s-extend γ.val s|) volume 0 T := (β.integrable.sub γ.integrable).abs.intervalIntegrable
    rw [intervalIntegral.integral_add hfi intervalIntegrable_const,
      intervalIntegral.integral_const]
    have hh := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := (T:ℝ)) (c := (0:ℝ)) (d := 1)
      le_rfl T.property.1 T.property.2.le (Eventually.of_forall (fun s => abs_nonneg (extend β.val s-extend γ.val s)))
      ((β.integrable.sub γ.integrable).abs.intervalIntegrable)
    simp only [sub_zero,smul_eq_mul]
    nlinarith only [hh]
  have hex : Real.exp ((stripDrift W γ T).rate*t) ≤ Real.exp ((stripDrift W γ T).rate*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (stripDrift W γ T).rate_pos.le)
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hex
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (hi0.trans hi)))

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem diffusion_uniqueness (W : BrownianSystem Ω) (γ : OrderParameter)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.law, ∀ t : ℝ≥0, t ≤ 1 → X t ω = diffusion W γ t ω := by
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hZ : IsProgressive ℱ (fun t ω => X t ω-W.driver t ω) := hX.1.sub W.driver_progressive
  filter_upwards [hX.2,W.driver_indistinguishable] with ω hω hB
  have hbefore (t : ℝ≥0) (ht : (t:ℝ) < 1) : X t ω = diffusion W γ t ω := by
    let T : Time := ⟨t,⟨t.coe_nonneg,ht⟩⟩
    let b := stripDrift W γ T
    have he := b.correction_unique_on ℱ W.driver_progressive hZ t ω
    have hfix : ∀ s ≤ t, X s ω-W.driver s ω =
        timePrimitive (b.action W.driver (fun r ω => X r ω-W.driver r ω)) s ω := by
      intro s hs
      have hst : (s:ℝ) ≤ t := hs
      have hs1 : (s:ℝ) ≤ 1 := hst.trans ht.le
      have hi := hω.2.2 (s:ℝ) ⟨s.coe_nonneg,hs1⟩
      simp only [Real.toNNReal_coe] at hi
      rw [hi,hB s,add_sub_cancel_left]
      unfold timePrimitive BoundedLipschitzDrift.action
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le s.coe_nonneg] at hr
      have hrt : ((Real.toNNReal r):ℝ) ≤ (T:ℝ) := by rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans hst
      dsimp only
      rw [add_sub_cancel,stripDrift_eq W γ T ⟨(Real.toNNReal r).coe_nonneg,hrt⟩,
        Real.coe_toNNReal _ hr.1]
    have hc := he hfix t le_rfl
    rw [diffusion_eq_strip W γ T t le_rfl]
    change X t ω = W.driver t ω+b.correction W.driver t ω
    rw [hc]
    ring
  intro t ht
  by_cases ht1 : (t:ℝ) < 1
  · exact hbefore t ht1
  have he : t=1 := le_antisymm ht (by exact_mod_cast not_lt.mp ht1)
  subst t
  have hi := hω.2.2 1 ⟨by norm_num,le_rfl⟩
  simp only [Real.toNNReal_one] at hi
  rw [hi,diffusion,hB 1]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hr
  by_cases hr1 : r<1
  · have hrr : ((Real.toNNReal r):ℝ) < 1 := by rw [Real.coe_toNNReal _ hr.1]; exact hr1
    dsimp only
    rw [rawFeedback_eq W γ _ hrr,Real.coe_toNNReal _ hr.1,
      hbefore (Real.toNNReal r) hrr,diffusion_eq_raw W γ _ hrr]
  · have hr_eq : r=1 := le_antisymm hr.2 (not_lt.mp hr1)
    subst r
    simp [extend]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.StrictMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_pos_of_interval_support {P : Measure Ω} {X : Ω → ℝ} {f : ℝ → ℝ}
    (hX : ∀ a b : ℝ, a < b → 0 < P {ξ | X ξ ∈ Ioo a b})
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (hi : Integrable (fun ξ => f (X ξ)) P)
    (hne : ∃ x, f x ≠ 0) : 0 < ∫ ξ, f (X ξ) ∂P := by
  obtain ⟨x,hx⟩ := hne
  have he : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp he
  apply (integral_pos_iff_support_of_nonneg (fun ξ => hn (X ξ)) hi).mpr
  apply (hX (x-ε) (x+ε) (by linarith)).trans_le
  apply measure_mono
  intro ξ hξ
  change f (X ξ) ≠ 0
  apply hball
  rw [Real.dist_eq,abs_lt]
  change x-ε < X ξ ∧ X ξ < x+ε at hξ
  constructor <;> linarith [hξ.1,hξ.2]

lemma curvature_not_identically_zero (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ∃ x, curvature W γ t x ≠ 0 := by
  by_contra hh
  push Not at hh
  have hV := value_contDiff W γ ht0 ht1
  have hG := (contDiff_infty_iff_deriv.mp hV).2
  have hg (x : ℝ) : gradient W γ t x=0 := by
    have hc := is_const_of_deriv_eq_zero (hG.differentiable (by simp)) hh x 0
    exact hc.trans (gradient_zero W γ ht0 ht1)
  have hv (x : ℝ) := is_const_of_deriv_eq_zero (hV.differentiable (by simp)) hg x 0
  have h := abs_le_value W γ t (value W γ t 0+1) ht1.le
  rw [hv (value W γ t 0+1)] at h
  have := le_abs_self (value W γ t 0+1)
  linarith

lemma third_not_identically_zero (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ∃ x, deriv (curvature W γ t) x ≠ 0 := by
  by_contra hh
  push Not at hh
  have hV := value_contDiff W γ ht0 ht1
  have hG := (contDiff_infty_iff_deriv.mp hV).2
  have hC := (contDiff_infty_iff_deriv.mp hG).2
  have hc (x : ℝ) : curvature W γ t x=curvature W γ t 0 :=
    is_const_of_deriv_eq_zero (hC.differentiable (by simp)) hh x 0
  let c := curvature W γ t 0
  have ha (x : ℝ) : HasDerivAt (fun y => gradient W γ t y-c*y) 0 x := by
    have hd := (hG.differentiable (by simp) x).hasDerivAt
    change HasDerivAt (gradient W γ t) (curvature W γ t x) x at hd
    have hdc := hd.sub ((hasDerivAt_id x).const_mul c)
    have hz : curvature W γ t x-c=0 := by rw [hc];dsimp only [c];ring
    rw [mul_one,hz] at hdc
    exact hdc
  have he (x : ℝ) : gradient W γ t x=c*x := by
    have h := is_const_of_deriv_eq_zero (fun y => (ha y).differentiableAt) (fun y => (ha y).deriv) x 0
    rw [gradient_zero W γ ht0 ht1,mul_zero,sub_zero] at h
    linarith
  have hz : c=0 := by
    by_contra hc0
    have hb := gradient_abs_le_one W γ t (2/c) ht1.le
    rw [he,mul_div_cancel₀ _ hc0] at hb
    norm_num at hb
  obtain ⟨x,hx⟩ := curvature_not_identically_zero W γ ht0 ht1
  exact hx ((hc x).trans hz)

lemma actual_jet_even_moment_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht0 : 0 < (t:ℝ)) (n k : ℕ) (hk : 0 < k)
    (hne : ∃ x, iteratedDeriv (n+1) (value W γ t) x ≠ 0) :
    0 < ∫ ξ, (iteratedDeriv (n+1) (value W γ t)
      (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ))^(2*k) ∂W.law := by
  let := W.isProbability
  have hs := contDiff_iteratedDeriv_infty (value_contDiff W γ t.property.1 t.property.2) (n+1)
  have hm : Measurable (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)) := by
    let ℱ := Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable)
    have ha : Measurable[ℱ (⟨t,t.property.1⟩:ℝ≥0)] (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)) :=
      (diffusion_progressive W γ).adapted (⟨t,t.property.1⟩:ℝ≥0)
    exact ha.mono (ℱ.le _) le_rfl
  obtain ⟨C,hC,hbound⟩ := value_uniform_derivative_bounds W γ t.property.1 t.property.2 n
  have hi : Integrable (fun ξ => (iteratedDeriv (n+1) (value W γ t)
      (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ))^(2*k)) W.law := by
    apply Integrable.mono' (integrable_const (μ := W.law) (C^(2*k)))
    · exact ((hs.continuous.measurable.comp hm).pow_const _).aestronglyMeasurable
    · filter_upwards [] with ξ
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound t ⟨t.property.1,le_rfl⟩ _) _
  apply integral_pos_of_interval_support
    (P := W.law) (X := diffusion W γ (⟨t,t.property.1⟩:ℝ≥0))
    (f := fun x => (iteratedDeriv (n+1) (value W γ t) x)^(2*k))
    (fun a b hab => diffusion_interval_pos W γ t ht0 hab)
    (hs.continuous.pow _) (fun x => by rw [pow_mul];exact pow_nonneg (pow_two_nonneg _) k) hi
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,(pow_ne_zero_iff (Nat.ne_of_gt (Nat.mul_pos (by decide) hk))).mpr hx⟩

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.JetFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactJet_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t x : ℝ) :
    HasDerivAt (compactJet W γ T n t) (compactJet W γ T (n+1) t x) x :=
  by
    have hh : ContDiff ℝ ∞ (compactJet W γ T n t) :=
      (((compactGradient_family W γ hT0 hT1).iteratedDeriv n).regular t).smooth
    have he : compactJet W γ T (n+1) t x=deriv (compactJet W γ T n t) x := by
      unfold compactJet
      rw [iteratedDeriv_succ]
    rw [he]
    exact (hh.differentiable (by simp) x).hasDerivAt

lemma deriv_compactJet (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t : ℝ) :
    deriv (compactJet W γ T n t)=compactJet W γ T (n+1) t :=
  funext (fun x => (compactJet_hasDerivAt W γ hT0 hT1 n t x).deriv)

lemma compactRate_jet_one (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 2 t x-
      compactCoeff γ T t*compactJet W γ T 0 t x*compactJet W γ T 1 t x := by
  simpa only [compactJet,iteratedDeriv_succ,iteratedDeriv_zero] using deriv_compactValueRate W γ hT0 hT1 t x

lemma compactRate_jet_two (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    iteratedDeriv 2 (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 3 t x-
      compactCoeff γ T t*((compactJet W γ T 1 t x)^2+compactJet W γ T 0 t x*compactJet W γ T 2 t x) := by
  have he : deriv (compactValueRate W γ T t)=fun y => -(1/2:ℝ)*compactJet W γ T 2 t y-
      compactCoeff γ T t*compactJet W γ T 0 t y*compactJet W γ T 1 t y := funext (compactRate_jet_one W γ hT0 hT1 t)
  have hd (n : ℕ) := compactJet_hasDerivAt W γ hT0 hT1 n t x
  have hh := ((hd 2).const_mul (-(1/2:ℝ))).sub (((hd 0).const_mul (compactCoeff γ T t)).mul (hd 1))
  have hdv := hh.deriv
  change deriv (fun y => -(1/2:ℝ)*compactJet W γ T 2 t y-
      compactCoeff γ T t*compactJet W γ T 0 t y*compactJet W γ T 1 t y) x = _ at hdv
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at ⊢
  rw [he,hdv]
  ring

lemma compactJetField_generator_one (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (compactJetField W γ hT0 hT1 1).generator (compactDrift W γ T) t x=
      -compactCoeff γ T t*(compactJet W γ T 1 t x)^2 := by
  dsimp only [TimeField.generator,compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1,
    compactRate_jet_two W γ hT0 hT1]
  change compactJet W γ T 2 t x*(compactCoeff γ T t*compactJet W γ T 0 t x)+_+_= _
  ring

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma curvatureField_generator (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (curvatureField W γ hT0 hT1).generator (compactDrift W γ T) t x=
      (secondCurvatureField W γ hT0 hT1 (compactCoeff γ T t)).f t x := by
  unfold curvatureField
  rw [TimeField.generator_mul,compactJetField_generator_one W γ hT0 hT1]
  dsimp only [compactJetField]
  rw [deriv_compactJet W γ hT0 hT1]
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

lemma curvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (curvatureField W γ hT0 hT1).f t x=(compactJet W γ T 1 t x)^2 := by
  dsimp only [curvatureField,TimeField.mul,compactJetField]
  ring

lemma secondCurvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) :
    (secondCurvatureField W γ hT0 hT1 c).f t x=
      (compactJet W γ T 2 t x)^2-2*c*(compactJet W γ T 1 t x)^3 := by
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.ThirdFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma hasDerivAt_of_right_on_Ioo {F G : ℝ → ℝ} {a b t : ℝ}
    (hF : Continuous F) (hG : Continuous G) (ht : t ∈ Ioo a b)
    (hd : ∀ s ∈ Ioo a b, HasDerivWithinAt F (G s) (Ioi s) s) :
    HasDerivAt F (G t) t := by
  have he (s : ℝ) (hs : s ∈ Ioo a b) : F s=(∫ r in a..s, G r)+F a := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1.le hF.continuousOn
      (fun r hr => hd r ⟨hr.1,hr.2.trans hs.2⟩) (hG.intervalIntegrable a s)
    linarith
  have hh := (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a t)
    hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).add_const (F a)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact he s hs

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma stripSecond_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) :
    Continuous (stripSecond W γ T c) := TimeField.expected_continuous _ _ _

lemma curvatureField_expected (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    (curvatureField W γ T.property.1 T.property.2).expected (stripDrift W γ T) W=stripA W γ T := by
  funext t
  unfold TimeField.expected stripA
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [curvatureField_eq]
  simp only [compactJet,iteratedDeriv_one]

lemma stripA_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) (hs : (s:ℝ) < T) :
    HasDerivWithinAt (stripA W γ T) (stripSecond W γ T (compactCoeff γ T s) s) (Ioi (s:ℝ)) s := by
  have hd := (curvatureField W γ T.property.1 T.property.2).expected_hasDerivWithinAt_right
    (stripDrift W γ T) W s hs (stripDrift_pathDrift_right W γ T s)
  rw [curvatureField_expected] at hd
  convert hd using 1 <;> try rfl
  unfold stripSecond TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Real.toNNReal_coe,stripDrift]
  exact (curvatureField_generator W γ T.property.1 T.property.2 (s:ℝ) _).symm

lemma stripA_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, compactCoeff γ T s=c) :
    HasDerivAt (stripA W γ T) (stripSecond W γ T c t) t := by
  apply hasDerivAt_of_right_on_Ioo (stripA_continuous W γ T) (stripSecond_continuous W γ T c) ht
  intro s hs
  have hs0 := ha.trans hs.1.le
  have hd := stripA_hasDerivWithinAt_right W γ T (Real.toNNReal s)
    (by rw [Real.coe_toNNReal _ hs0]; exact hs.2.trans_le hbT)
  simpa only [Real.coe_toNNReal _ hs0,hc s hs] using hd

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.Curvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactJet_eq_value (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) (n : ℕ) (x : ℝ) :
    compactJet W γ T n t x=iteratedDeriv (n+1) (value W γ t) x := by
  unfold compactJet compactGradient gradient
  rw [stripClamp_eq ht,iteratedDeriv_succ']

lemma stripSecond_eq_actual (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (htT : t ≤ T) (c : ℝ) :
    stripSecond W γ T c t = ∫ ξ, (actualJet W γ t 3 ξ)^2-2*c*(actualJet W γ t 2 ξ)^3 ∂W.law := by
  unfold stripSecond TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [secondCurvatureField_eq]
  have heNN : Real.toNNReal (t:ℝ)=(⟨t,t.property.1⟩:ℝ≥0) := by ext;exact Real.coe_toNNReal _ t.property.1
  rw [heNN]
  have hd := diffusion_eq_strip W γ T (⟨t,t.property.1⟩:ℝ≥0) htT ξ
  rw [← hd,compactJet_eq_value W γ T ⟨t.property.1,htT⟩,
    compactJet_eq_value W γ T ⟨t.property.1,htT⟩]
  rfl

lemma actualThirdSquare_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) : 0 < ∫ ξ, (actualJet W γ t 3 ξ)^2 ∂W.law := by
  apply actual_jet_even_moment_pos W γ t ht 2 1 (by norm_num)
  have hn := third_not_identically_zero W γ t.property.1 t.property.2
  change ∃ x, deriv (deriv (deriv (value W γ t))) x ≠ 0 at hn
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hn

lemma stripSecond_zero_pos (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) : 0 < stripSecond W γ T 0 t := by
  rw [stripSecond_eq_actual W γ T t htT]
  simp only [mul_zero,zero_mul,sub_zero]
  exact actualThirdSquare_pos W γ t ht

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.GapCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactCoeff_constant (γ : OrderParameter) (T : Time) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    ∀ s ∈ Ioo a b, compactCoeff γ T s=c := by
  intro s hs
  rw [compactCoeff,stripClamp_eq ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩]
  exact hc s hs

lemma curvatureMoment_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    HasDerivAt (curvatureMoment W γ) (stripSecond W γ T c t) t := by
  have hd := stripA_hasDerivAt_on_constant W γ T ha hbT ht (compactCoeff_constant γ T ha hbT hc)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hbT)] with s hs
  exact (stripA_eq_curvatureMoment W γ T ⟨hs.1.le,hs.2.le⟩).symm

theorem zero_gap_curvature (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=0) :
    ∀ t ∈ Ioo a b, 0 < deriv (curvatureMoment W γ) t := by
  intro t ht
  let T : Time := ⟨b,⟨ha.trans hab.le,hb⟩⟩
  let τ : Time := ⟨t,⟨ha.trans ht.1.le,ht.2.trans hb⟩⟩
  rw [(curvatureMoment_hasDerivAt_on_constant W γ T ha le_rfl ht hc).deriv]
  exact stripSecond_zero_pos W γ T τ (ha.trans_lt ht.1) ht.2.le

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma parameterStieltjes_atBot (γ : OrderParameter) :
    Tendsto (parameterStieltjes γ) atBot (𝓝 (γ.val ⊥)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (⊥ : Time)] with t ht
  have he : t=⊥ := le_antisymm ht bot_le
  subst t
  rfl

lemma parameterMeasure_isStieltjes (γ : OrderParameter) : IsStieltjesMeasure γ (parameterMeasure γ) := by
  intro t
  rw [parameterMeasure,Measure.add_apply,(parameterStieltjes γ).measure_Iic (parameterStieltjes_atBot γ),
    Measure.smul_apply,Measure.dirac_apply' _ measurableSet_Iic]
  have hbot : (⊥ : Time) ∈ Iic t := by change (⊥ : Time) ≤ t; exact bot_le
  simp only [Set.indicator_of_mem hbot,Pi.one_apply,smul_eq_mul,mul_one]
  change ENNReal.ofReal (γ.val t-γ.val ⊥)+ENNReal.ofReal (γ.val ⊥)=ENNReal.ofReal (γ.val t)
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (γ.monotone bot_le)) (γ.nonneg ⊥),sub_add_cancel]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.Closure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ZeroTemperatureSK.SupportDeterministic

namespace IsStieltjesMeasure

variable {γ : ℝ → ℝ} {μ : Measure Time}

lemma cdf_add_Ioc (hμ : IsStieltjesMeasure γ μ) {a b : Time} (hab : a ≤ b) :
    ENNReal.ofReal (γ a) + μ (Ioc a b) = ENNReal.ofReal (γ b) := by
  rw [← hμ a, ← hμ b, ← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
    Iic_union_Ioc_eq_Iic hab]

lemma eq_cdf_of_measure_Ioc_zero (hμ : IsStieltjesMeasure γ μ)
    (hγ : IsOrderParameter γ) {a b : Time} (hab : a ≤ b)
    (hz : μ (Ioc a b) = 0) : γ a = γ b := by
  have he := hμ.cdf_add_Ioc hab
  rw [hz, add_zero] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (hγ.nonneg a a.property) (hγ.nonneg b b.property)).mp he

lemma measure_zero_of_disjoint_support {s : Set Time}
    (hs : Disjoint s μ.support) : μ s = 0 := by
  apply measure_mono_null (Set.disjoint_left.mp hs) μ.measure_compl_support

lemma eq_cdf_of_support_free (hμ : IsStieltjesMeasure γ μ)
    (hγ : IsOrderParameter γ) {a b : Time} (hab : a ≤ b)
    (hs : Disjoint (Ioc a b) μ.support) : γ a = γ b :=
  hμ.eq_cdf_of_measure_Ioc_zero hγ hab (measure_zero_of_disjoint_support hs)

lemma lt_cdf_of_full_support (hμ : IsStieltjesMeasure γ μ)
    (hS : μ.support = univ) {a b : Time} (hab : a < b) : γ a < γ b := by
  let c : Time := ⟨((a : ℝ) + b) / 2, by
    constructor
    · linarith [a.property.1, b.property.1]
    · linarith [a.property.2, b.property.2]⟩
  have hac : a < c := by change (a : ℝ) < ((a : ℝ) + b) / 2; change (a : ℝ) < b at hab; linarith
  have hcb : c < b := by change ((a : ℝ) + b) / 2 < b; change (a : ℝ) < b at hab; linarith
  have hcS : c ∈ μ.support := by rw [hS]; trivial
  have hpos : 0 < μ (Ioc a b) :=
    lt_of_lt_of_le ((μ.mem_support_iff_forall c).mp hcS _ (Ioo_mem_nhds hac hcb))
      (measure_mono Ioo_subset_Ioc_self)
  have hlt : ENNReal.ofReal (γ a) < ENNReal.ofReal (γ b) := by
    rw [← hμ.cdf_add_Ioc hab.le]
    exact ENNReal.lt_add_right ENNReal.ofReal_ne_top hpos.ne'
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1

lemma strictMonoOn_of_full_support (hμ : IsStieltjesMeasure γ μ)
    (hS : μ.support = univ) : StrictMonoOn γ (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  exact hμ.lt_cdf_of_full_support hS (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hab

end IsStieltjesMeasure

lemma exists_support_gap {μ : Measure Time} {x : Time}
    (hx : x ∉ μ.support) (hright : ∃ B ∈ μ.support, x < B) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b < 1 ∧ (a = 0 ∨ InSupport μ a) ∧
      InSupport μ b ∧ ∀ t ∈ Ioo a b, ¬ InSupport μ t := by
  obtain ⟨F, hF, hpre⟩ :=
    (Topology.IsInducing.subtypeVal (t := Ico (0 : ℝ) 1)).isClosed_iff.mp μ.isClosed_support
  have hFiff (t : Time) : (t : ℝ) ∈ F ↔ t ∈ μ.support := by
    change t ∈ (Subtype.val ⁻¹' F) ↔ _
    rw [hpre]
  obtain ⟨B, hBS, hxB⟩ := hright
  have hcompactA : IsCompact ({0} ∪ (F ∩ Icc (0 : ℝ) x)) :=
    isCompact_singleton.union (isCompact_Icc.inter_left hF)
  obtain ⟨a, ha⟩ := hcompactA.exists_isGreatest (by exact ⟨0, Or.inl rfl⟩)
  have hcompactB : IsCompact (F ∩ Icc (x : ℝ) B) :=
    isCompact_Icc.inter_left hF
  obtain ⟨b, hb⟩ := hcompactB.exists_isLeast
    ⟨B, (hFiff B).mpr hBS, hxB.le, le_rfl⟩
  have ha0 : 0 ≤ a := ha.2 (Or.inl rfl)
  have hax : a ≤ x := by
    rcases ha.1 with heq | hm
    · simpa only [mem_singleton_iff] using heq ▸ x.property.1
    · exact hm.2.2
  have hb1 : b < 1 := hb.1.2.2.trans_lt B.property.2
  have hxb : (x : ℝ) < b := by
    refine lt_of_le_of_ne hb.1.2.1 ?_
    intro heq
    apply hx
    apply (hFiff x).mp
    simpa [heq] using hb.1.1
  refine ⟨a, b, ha0, hax.trans_lt hxb, hb1, ?_, ?_, ?_⟩
  · rcases ha.1 with heq | hm
    · exact Or.inl heq
    · exact Or.inr ⟨⟨ha0, hax.trans_lt x.property.2⟩,
        (hFiff ⟨a, ⟨ha0, hax.trans_lt x.property.2⟩⟩).mp hm.1⟩
  · exact ⟨⟨x.property.1.trans hxb.le, hb1⟩,
      (hFiff ⟨b, ⟨x.property.1.trans hxb.le, hb1⟩⟩).mp hb.1.1⟩
  · intro t ht hts
    obtain ⟨ht01, hts⟩ := hts
    have htF : t ∈ F := (hFiff ⟨t, ht01⟩).mpr hts
    by_cases htx : t ≤ x
    · exact (not_lt_of_ge (ha.2 (Or.inr ⟨htF, ht01.1, htx⟩))) ht.1
    · exact (not_lt_of_ge (hb.2 ⟨htF, le_of_not_ge htx, ht.2.le.trans hb.1.2.2⟩)) ht.2

lemma support_cofinal_of_no_terminal_plateau {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    (hend : ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧
      ∀ t ∈ Ioo a 1, γ t = c) (x : Time) :
    ∃ B ∈ μ.support, x < B := by
  by_contra hn
  push Not at hn
  let d : Time := ⟨((x : ℝ) + 1) / 2, by
    constructor <;> linarith [x.property.1, x.property.2]⟩
  apply hend
  refine ⟨x, γ d, x.property.1, x.property.2, hγ.nonneg d d.property, ?_⟩
  intro t ht
  let t' : Time := ⟨t, ⟨x.property.1.trans ht.1.le, ht.2⟩⟩
  have hxd : x < d := by change (x : ℝ) < ((x : ℝ)+1)/2; linarith [x.property.2]
  have heq {u v : Time} (hu : x < u) (hv : x < v) (huv : u ≤ v) :
      γ u = γ v := by
    apply hμ.eq_cdf_of_support_free hγ huv
    rw [Set.disjoint_left]
    intro z hz hzs
    exact (not_lt_of_ge (hn z hzs)) (hu.trans hz.1)
  change γ t' = γ d
  rcases le_total t' d with htd | hdt
  · exact heq ht.1 hxd htd
  · exact (heq hxd ht.1 hdt).symm

lemma constant_on_support_gap {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hgap : ∀ t ∈ Ioo a b, ¬ InSupport μ t) :
    ∃ c, 0 ≤ c ∧ ∀ t ∈ Ioo a b, γ t = c := by
  let d : Time := ⟨(a+b)/2, by constructor <;> linarith⟩
  have hd : (d : ℝ) ∈ Ioo a b := by change a < (a+b)/2 ∧ (a+b)/2 < b; constructor <;> linarith
  refine ⟨γ d, hγ.nonneg d d.property, ?_⟩
  have heq {u v : Time} (hu : (u : ℝ) ∈ Ioo a b)
      (hv : (v : ℝ) ∈ Ioo a b) (huv : u ≤ v) : γ u = γ v := by
    apply hμ.eq_cdf_of_support_free hγ huv
    rw [Set.disjoint_left]
    intro z hz hzs
    exact hgap z ⟨hu.1.trans (show (u : ℝ) < z from hz.1), (show (z : ℝ) ≤ v from hz.2).trans_lt hv.2⟩ ⟨z.property, hzs⟩
  intro t ht
  let t' : Time := ⟨t, ⟨ha.trans ht.1.le, ht.2.trans hb⟩⟩
  change γ t' = γ d
  rcases le_total t' d with htd | hdt
  · exact heq ht hd htd
  · exact (heq hd ht hdt).symm

lemma zero_on_initial_support_gap {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ) {b : ℝ}
    (hb : b < 1) (h0 : ¬ InSupport μ 0)
    (hgap : ∀ t ∈ Ioo 0 b, ¬ InSupport μ t) :
    ∀ t ∈ Ioo 0 b, γ t = 0 := by
  intro t ht
  let t' : Time := ⟨t, ⟨ht.1.le, ht.2.trans hb⟩⟩
  have hm : μ (Iic t') = 0 := by
    apply IsStieltjesMeasure.measure_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro z hz hzs
    by_cases hz0 : (z : ℝ) = 0
    · exact h0 (hz0 ▸ ⟨z.property, hzs⟩)
    · exact hgap z ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0), hz.trans_lt ht.2⟩
        ⟨z.property, hzs⟩
  rw [hμ t', ENNReal.ofReal_eq_zero] at hm
  exact le_antisymm hm (hγ.nonneg t' t'.property)

lemma IsStieltjesMeasure.finiteOnCompacts {γ : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ) : IsFiniteMeasureOnCompacts μ := by
  constructor
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨b, hb⟩ := (hK.image continuous_subtype_val).exists_isGreatest (hne.image Subtype.val)
    obtain ⟨b', hb'K, rfl⟩ := hb.1
    apply lt_of_le_of_lt (measure_mono (t := Iic b') ?_)
    · rw [hμ b']; exact ENNReal.ofReal_lt_top
    · intro t ht; exact hb.2 ⟨t, ht, rfl⟩

lemma isCompact_time_Iic (b : Time) : IsCompact (Iic b) := by
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' Iic b = Icc (0 : ℝ) b := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u.property.1, hu⟩
    · intro ht
      exact ⟨⟨t, ⟨ht.1, ht.2.trans_lt b.property.2⟩⟩, ht.2, rfl⟩
  rw [heq]
  exact isCompact_Icc

end ZeroTemperatureSK.SupportDeterministic

namespace ZeroTemperatureSK.SupportDeterministic.Variation

lemma continuous_zero_on_support_of_integral_nonpos
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    {ν : Measure Y} {F : Y → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F ν) (hI : ∫ x, F x ∂ν ≤ 0) :
    ∀ x ∈ ν.support, F x = 0 := by
  have hz : ∫ x, F x ∂ν = 0 := le_antisymm hI (integral_nonneg hF0)
  have hae : F =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hz
  intro x hx
  by_contra hne
  have hn : {y | F y ≠ 0} ∈ 𝓝 x :=
    (isOpen_ne.preimage hF).mem_nhds hne
  have hp : 0 < ν {y | F y ≠ 0} := (ν.mem_support_iff_forall x).mp hx _ hn
  have hzset : ν {y | F y ≠ 0} = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using hae
  exact hp.ne' hzset

theorem zero_on_support_of_compact_mass_removal {γ G : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hremove : ∀ K : Set Time, IsCompact K → ∫ t in K, G t ∂μ ≤ 0) :
    ∀ t, InSupport μ t → G t = 0 := by
  let : IsFiniteMeasureOnCompacts μ := hμ.finiteOnCompacts
  have hcont : Continuous (fun t : Time => G t) :=
    continuousOn_iff_continuous_domRestrict.mp hGc
  intro t ht
  obtain ⟨ht, hts⟩ := ht
  let x : Time := ⟨t,ht⟩
  let b : Time := ⟨(t+1)/2, by constructor <;> linarith [ht.1, ht.2]⟩
  have hxb : x < b := by change t < (t+1)/2; linarith [ht.2]
  have hxint : x ∈ interior (Iic b) :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (Iio_mem_nhds hxb) Iio_subset_Iic_self)
  have hxs : x ∈ (μ.restrict (Iic b)).support := μ.interior_inter_support ⟨hxint, hts⟩
  exact continuous_zero_on_support_of_integral_nonpos hcont
    (fun y => hG0 y y.property)
    (hcont.continuousOn.integrableOn_compact (isCompact_time_Iic b))
    (hremove (Iic b) (isCompact_time_Iic b)) x hxs

lemma value_contact_of_potential_min {q G : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hGs : G s = 0) (hGd : HasDerivAt G (s - q s) s) : q s = s := by
  have hmin : IsLocalMin G s := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    rw [hGs]
    exact hG0 t ⟨ht.1.le, ht.2⟩
  have hzero := hmin.hasDerivAt_eq_zero hGd
  linarith

lemma derivative_contact_of_potential_min {q G : ℝ → ℝ} {s d : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hGs : G s = 0) (hqs : q s = s)
    (hqd : HasDerivWithinAt q d (Ici s) s)
    (hGd : ∀ t ∈ Ioo s 1, HasDerivAt G (t - q t) t) : d ≤ 1 := by
  by_contra hd
  have hd : 1 < d := lt_of_not_ge hd
  have hsel : Ici s \ {s} = Ioi s := by ext t; simp
  have hlim : Tendsto (slope q s) (𝓝[>] s) (𝓝 d) := by
    simpa only [hsel] using (hasDerivWithinAt_iff_tendsto_slope.mp hqd)
  have he : ∀ᶠ t in 𝓝[>] s, 1 < slope q s t ∧ t < 1 :=
    (hlim.eventually (Ioi_mem_nhds hd)).and
      (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hs.2))
  obtain ⟨b, hsb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  obtain ⟨y, hsy, hyb⟩ := exists_between (show s < b from hsb)
  have hy1 : y < 1 := (hb ⟨hsy, hyb⟩).2
  have hanti : StrictAntiOn G (Icc s y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s y)
      (hGc.mono (by intro t ht; exact ⟨hs.1.trans ht.1, ht.2.trans_lt hy1⟩))
    intro t ht
    rw [interior_Icc] at ht
    have hslt := (hb ⟨ht.1, ht.2.trans hyb⟩).1
    have hgt : t < q t := by
      rw [slope_def_field, hqs, lt_div_iff₀ (sub_pos.mpr ht.1)] at hslt
      linarith
    rw [(hGd t ⟨ht.1, ht.2.trans hy1⟩).deriv]
    exact sub_neg.mpr hgt
  have hneg := hanti (left_mem_Icc.mpr hsy.le) (right_mem_Icc.mpr hsy.le) hsy
  rw [hGs] at hneg
  exact (not_lt_of_ge (hG0 y ⟨hs.1.trans hsy.le, hy1⟩)) hneg

theorem contact_conditions {γ q q' G : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hremove : ∀ K : Set Time, IsCompact K → ∫ t in K, G t ∂μ ≤ 0)
    (hq0 : q 0 = 0)
    (hqderiv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt q (q' t) (Ici t) t)
    (hGderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G (t - q t) t) :
    ∀ t, InSupport μ t → q t = t ∧ q' t ≤ 1 := by
  intro t ht
  have ht01 : t ∈ Ico (0 : ℝ) 1 := ht.choose
  have hGt : G t = 0 := zero_on_support_of_compact_mass_removal hμ hGc hG0 hremove t ht
  have hqt : q t = t := by
    rcases eq_or_lt_of_le ht01.1 with ht0 | htpos
    · simpa only [← ht0] using hq0
    · exact value_contact_of_potential_min ⟨htpos, ht01.2⟩ hG0 hGt
        (hGderiv t ⟨htpos, ht01.2⟩)
  exact ⟨hqt, derivative_contact_of_potential_min ht01 hGc hG0 hGt hqt (hqderiv t ht01)
    (fun s hs => hGderiv s ⟨ht01.1.trans_lt hs.1, hs.2⟩)⟩

end ZeroTemperatureSK.SupportDeterministic.Variation

namespace ZeroTemperatureSK.SupportDeterministic.Variation

theorem no_gap_of_derivative_lt_one {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hbound : ∀ t ∈ Ioo a b, q' t < 1) : False := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope q q' hab hc hd
  rw [ha, hb, div_self (sub_ne_zero.mpr hab.ne')] at heq
  exact (hbound t ht).ne heq

theorem no_gap_of_strictConvex_derivative {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hconvex : StrictConvexOn ℝ (Icc a b) q')
    (hda : q' a ≤ 1) (hdb : q' b ≤ 1) : False := by
  apply no_gap_of_derivative_lt_one hab hc hd ha hb
  intro t ht
  exact (hconvex.lt_on_openSegment
      (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
      hab.ne (Ioo_subset_openSegment ht)).trans_le (max_le hda hdb)

theorem no_positive_constant_gap {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hc' : ContinuousOn q' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hcurvature : ∀ t ∈ Ioo a b, 0 < (deriv^[2] q') t)
    (hda : q' a ≤ 1) (hdb : q' b ≤ 1) : False := by
  apply no_gap_of_strictConvex_derivative hab hc hd ha hb ?_ hda hdb
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b) hc'
  simpa only [interior_Icc] using hcurvature

theorem no_zero_constant_gap {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hc' : ContinuousOn q' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hcurvature : ∀ t ∈ Ioo a b, 0 < deriv q' t)
    (hdb : q' b ≤ 1) : False := by
  have hm : StrictMonoOn q' (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hc'
      (by simpa only [interior_Icc] using hcurvature)
  apply no_gap_of_derivative_lt_one hab hc hd ha hb
  intro t ht
  exact (hm (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hab.le) ht.2).trans_le hdb

end ZeroTemperatureSK.SupportDeterministic.Variation

namespace ZeroTemperatureSK.SupportDeterministic.Variation

theorem full_support_of_contact_and_gap_curvature
    {γ q q' : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    (hc : ContinuousOn q (Ico (0 : ℝ) 1))
    (hc' : ContinuousOn q' (Ico (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hq0 : q 0 = 0)
    (hcontact : ∀ t, InSupport μ t → q t = t ∧ q' t ≤ 1)
    (hend : ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧
      ∀ t ∈ Ioo a 1, γ t = c)
    (hpositive : ∀ a b c : ℝ, 0 ≤ a → a < b → b < 1 → 0 < c →
      (∀ t ∈ Ioo a b, γ t = c) → ∀ t ∈ Ioo a b, 0 < (deriv^[2] q') t)
    (hzero : ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      (∀ t ∈ Ioo a b, γ t = 0) → ∀ t ∈ Ioo a b, 0 < deriv q' t) :
    μ.support = univ ∧ StrictMonoOn γ (Ico (0 : ℝ) 1) ∧
      ∀ t ∈ Ico (0 : ℝ) 1, q t = t := by
  have hS : μ.support = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨a, b, ha, hab, hb, haS, hbS, hgap⟩ :=
      exists_support_gap hx (support_cofinal_of_no_terminal_plateau hγ hμ hend x)
    have hsub : Icc a b ⊆ Ico (0 : ℝ) 1 := by
      intro t ht; exact ⟨ha.trans ht.1, ht.2.trans_lt hb⟩
    have hderiv : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t := by
      intro t ht; exact hd t ⟨ha.trans_lt ht.1, ht.2.trans hb⟩
    have hqa : q a = a := by
      rcases haS with rfl | haS
      · exact hq0
      · exact (hcontact a haS).1
    have hqb : q b = b := (hcontact b hbS).1
    have hdb : q' b ≤ 1 := (hcontact b hbS).2
    obtain ⟨c, hc0, hconstant⟩ := constant_on_support_gap hγ hμ ha hab hb hgap
    rcases eq_or_lt_of_le hc0 with heq | hpos
    · apply no_zero_constant_gap hab (hc.mono hsub) (hc'.mono hsub) hderiv hqa hqb
        (hzero a b ha hab hb (by simpa only [← heq] using hconstant)) hdb
    · have hda : q' a ≤ 1 := by
        by_cases haS' : InSupport μ a
        · exact (hcontact a haS').2
        · have ha0 : a = 0 := haS.resolve_right haS'
          subst a
          have hz := zero_on_initial_support_gap hγ hμ hb haS' hgap
          have hmid : b / 2 ∈ Ioo (0 : ℝ) b := by constructor <;> linarith
          have heq : c = 0 := (hconstant _ hmid).symm.trans (hz _ hmid)
          exact False.elim (hpos.ne' heq)
      exact no_positive_constant_gap hab (hc.mono hsub) (hc'.mono hsub)
        hderiv hqa hqb (hpositive a b c ha hab hb hpos hconstant) hda hdb
  refine ⟨hS, hμ.strictMonoOn_of_full_support hS, ?_⟩
  intro t ht
  exact (hcontact t ⟨ht, by rw [hS]; trivial⟩).1

theorem derivative_eq_one_of_full_contact {q q' : ℝ → ℝ}
    (hq : ∀ t ∈ Ico (0 : ℝ) 1, q t = t)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hd0 : HasDerivWithinAt q (q' 0) (Ici (0 : ℝ)) 0) :
    ∀ t ∈ Ico (0 : ℝ) 1, q' t = 1 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht0 | htpos
  · subst t
    have heq : q =ᶠ[𝓝[Ici (0 : ℝ)] 0] id := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
      exact hq x ⟨hx, hx1⟩
    have hid : HasDerivWithinAt q 1 (Ici (0 : ℝ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq heq (hq 0 (by simp))
    exact (hd0.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hid.derivWithin (uniqueDiffWithinAt_Ici 0))
  · have heq : q =ᶠ[𝓝 t] id := by
      filter_upwards [Ioo_mem_nhds htpos ht.2] with x hx
      exact hq x ⟨hx.1.le, hx.2⟩
    have hid : HasDerivAt q 1 t := (hasDerivAt_id t).congr_of_eventuallyEq heq
    exact (hd t ⟨htpos, ht.2⟩).unique hid

end ZeroTemperatureSK.SupportDeterministic.Variation

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.CDFParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma OrderParameter.addCDF_difference (γ : OrderParameter) (ν : Measure Time) [IsFiniteMeasure ν] (t : ℝ) :
    extend (γ.addCDF ν).val t-extend γ.val t=extend (finiteCDF ν) t := by
  change extend (fun t => γ.val t+finiteCDF ν t) t-extend γ.val t=_
  rw [extend_add_fun]
  ring

lemma OrderParameter.removeCDF_difference (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) (t : ℝ) :
    extend (γ.removeCDF hμ hν).val t-extend γ.val t= -extend (finiteCDF ν) t := by
  change extend (fun t => γ.val t-finiteCDF ν t) t-extend γ.val t=_
  rw [extend_sub_fun]
  ring

lemma OrderParameter.original_deterministic (γ : OrderParameter) :
    SupportDeterministic.IsOrderParameter (extend γ.val) where
  nonneg := fun t _ => γ.extend_nonneg t
  monotone := by
    intro a ha b hb hab
    simpa only [extend,dite_eq_left ha,dite_eq_left hb] using γ.monotone (show (⟨a,ha⟩ : Time) ≤ ⟨b,hb⟩ from hab)
  rightContinuous := by
    intro t ht
    let T : ℝ := (t+1)/2
    have hT0 : 0 ≤ T := by dsimp [T];linarith [ht.1,ht.2]
    have hT1 : T < 1 := by dsimp [T];linarith [ht.1,ht.2]
    have htT : t < T := by dsimp [T];linarith [ht.2]
    have hc := compactCoeff_rightContinuous γ hT0 hT1 t
    have he : compactCoeff γ T =ᶠ[𝓝[Ici t] t] extend γ.val := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      rw [compactCoeff,stripClamp_eq ⟨ht.1.trans hs,hsT.le⟩]
    have hh := hc.tendsto.congr' he
    change Tendsto (extend γ.val) (𝓝[Ici t] t) (𝓝 (extend γ.val t))
    simpa only [compactCoeff,stripClamp_eq ⟨ht.1,htT.le⟩] using hh
  integrable := γ.integrable.integrableOn

lemma stieltjes_deterministic (γ : OrderParameter) {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    SupportDeterministic.IsStieltjesMeasure (extend γ.val) μ := by
  intro t
  simpa only [extend,dite_eq_left t.property] using hμ t

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma finiteCDF_fubini {H : ℝ → ℝ} (hH : IntervalIntegrable H volume 0 1)
    (ν : Measure Time) [IsFiniteMeasure ν] :
    (∫ t in (0:ℝ)..1, extend (finiteCDF ν) t*H t)=∫ r : Time, (∫ t in (r:ℝ)..1, H t) ∂ν := by
  let κ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  let F : ℝ → Time → ℝ := fun t r => if (r:ℝ) ≤ t then H t else 0
  have hHi : Integrable H κ := hH.1
  have hs : MeasurableSet {p : ℝ × Time | (p.2:ℝ) ≤ p.1} :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_fst).measurableSet
  have hFi : Integrable (Function.uncurry F) (κ.prod ν) := by
    have he : Function.uncurry F = {p : ℝ × Time | (p.2:ℝ) ≤ p.1}.indicator (fun p => H p.1) := by
      funext p
      rfl
    rw [he]
    exact (hHi.comp_fst ν).indicator hs
  have hleft : (∫ t in (0:ℝ)..1, extend (finiteCDF ν) t*H t)=∫ t, ∫ r, F t r ∂ν ∂κ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with t ht ht1
    have htt : t ∈ Ico (0:ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 ht1⟩
    rw [extend,dite_eq_left htt,finiteCDF_integral,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with r
    change (if r ≤ (⟨t,htt⟩ : Time) then (1:ℝ) else 0)*H t=(if (r:ℝ) ≤ t then H t else 0)
    by_cases hr : (r:ℝ) ≤ t <;> simp [hr,show (r ≤ (⟨t,htt⟩ : Time)) ↔ (r:ℝ) ≤ t from Iff.rfl]
  have hright (r : Time) : (∫ t, F t r ∂κ)=∫ t in (r:ℝ)..1, H t := by
    have he : (∫ t, F t r ∂κ)=∫ t, (Ioi (r:ℝ)).indicator H t ∂κ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (volume.ae_ne (r:ℝ))] with t htr
      simp only [F,indicator_apply,mem_Ioi]
      simp only [le_iff_lt_or_eq,or_iff_left (Ne.symm htr)]
    rw [he,integral_indicator measurableSet_Ioi]
    change (∫ t, H t ∂((volume.restrict (Ioc (0:ℝ) 1)).restrict (Ioi (r:ℝ))))=_
    rw [Measure.restrict_restrict measurableSet_Ioi]
    have heS : Ioi (r:ℝ) ∩ Ioc (0:ℝ) 1=Ioc (r:ℝ) 1 := by
      ext t
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · exact fun h => ⟨h.1,lt_of_le_of_lt r.property.1 h.1,h.2⟩
    rw [heS,intervalIntegral.integral_of_le r.property.2.le]
  rw [hleft,integral_integral_swap hFi]
  exact integral_congr_ae (Eventually.of_forall hright)

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.TerminalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma parameter_bound_of_terminal_plateau (γ : OrderParameter) {a c : ℝ} (ha : a < 1)
    (hc : ∀ t ∈ Ioo a 1, extend γ.val t=c) : ∀ t : Time, γ.val t ≤ c := by
  intro t
  let s : ℝ := (max (t:ℝ) a+1)/2
  have hm : max (t:ℝ) a < 1 := max_lt t.property.2 ha
  have hts : (t:ℝ) ≤ s := by dsimp [s];linarith [le_max_left (t:ℝ) a]
  have has : a < s := by dsimp [s];linarith [le_max_right (t:ℝ) a]
  have hs1 : s < 1 := by dsimp [s];linarith
  have hs : s ∈ Ico (0:ℝ) 1 := ⟨t.property.1.trans hts,hs1⟩
  have hh := hc s ⟨has,hs1⟩
  rw [extend,dite_eq_left hs] at hh
  exact (γ.monotone (a := t) (b := ⟨s,hs⟩) hts).trans_eq hh

lemma finite_terminal_curvature_bound {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {D t b : ℝ}
    (ht0 : 0 ≤ t) (htb : t < b) (hb : b ≤ (N:ℝ)*h) (hD : 0 ≤ D)
    (hc : ∀ r ∈ Icc t b, finiteCoeff c h N i r ≤ D)
    (hsmall : 8*kernelConstant*D*Real.sqrt (b-t) ≤ 1/2) (x : ℝ) :
    |deriv (deriv (finiteValue c h f N i t)) x| ≤ 2*kernelConstant/Real.sqrt (b-t) := by
  let V := fun r => deriv (finiteValue c h f N i r)
  let G := finiteBurgersSource c h f N i
  have hV := finiteGradient_family hf hLip c h N i
  have hG := finiteBurgersSource_family hf hLip c h N i
  obtain ⟨A₀,hA₀⟩ := hG.bound
  obtain ⟨B₀,hB₀⟩ := hG.deriv.bound
  obtain ⟨C₀,hC₀⟩ := hV.deriv.bound
  have hu (r x : ℝ) : |V r x| ≤ 1 := by
    simpa only [V,Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i r)
  have hsource (r : ℝ) (hr : r ∈ Icc t b) (z : ℝ) : |G r z| ≤ D*|deriv (V r) z|+0 := by
    have hh := iteratedDeriv_finiteBurgersSource_bound hf hLip c h N i 0
      (by norm_num : (0:ℝ) ≤ 1) hD (hc r hr) (fun j hj y => by
        have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
        subst j
        exact hu r y) z
    simpa only [G,V,iteratedDeriv_zero,iteratedDeriv_one,Finset.range_zero,Finset.sum_empty,mul_zero,zero_mul] using hh
  have hh := uniform_gradient_bound_of_mild htb (by norm_num : (0:ℝ) ≤ 1) hD (by norm_num : (0:ℝ) ≤ 0)
    (hV.regular b) hG.measurable hG.regular hA₀ hB₀ (fun r _ z => hC₀ r z) (hu b) hsource
    (fun r hr z => finiteGradient_mild hf hLip c h N i (ht0.trans hr.1) hr.2.le hb z) hsmall x
  simpa only [V,mul_zero,zero_mul,add_zero,mul_one] using hh

lemma approxGamma_global_cap (γ : OrderParameter) {D : ℝ} (hcap : ∀ t : Time, γ.val t ≤ D)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : approxGamma γ n s ≤ D := by
  obtain ⟨j,hj,he,_,_⟩ := finiteCoeff_sample (approxCoeff γ n) (approxMesh_pos n) (n+1) 0 hs.1
    (by rw [approxMesh_horizon];exact hs.2) (by omega)
  change finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D
  rw [he]
  simpa only [Nat.zero_add,approxCoeff_eq γ n j hj] using hcap ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩

lemma curvature_terminal_bound (W : BrownianSystem Ω) (γ : OrderParameter) {D t : ℝ}
    (hD : 0 ≤ D) (hcap : ∀ s : Time, γ.val s ≤ D) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsmall : 8*kernelConstant*D*Real.sqrt (1-t) ≤ 1/2) (x : ℝ) :
    |curvature W γ t x| ≤ 2*kernelConstant/Real.sqrt (1-t) := by
  have hl := (approxValue_derivative_uniform_spatial W γ ht0 ht1 2).tendsto_at x |>.abs
  have hb (n : ℕ) : |iteratedDeriv 2 (approxValue γ n t) x| ≤ 2*kernelConstant/Real.sqrt (1-t) := by
    have hh := finite_terminal_curvature_bound (regularDatum_softAbs (M := ((n+1:ℕ):ℝ)) (by positivity)) (softAbs_lipschitz (M := ((n+1:ℕ):ℝ)) (by positivity))
      (approxCoeff γ n) (approxMesh n) (n+1) 0 ht0 ht1 (by rw [approxMesh_horizon]) hD
      (fun r hr => approxGamma_global_cap γ hcap n ⟨ht0.trans hr.1,hr.2⟩) hsmall x
    simpa only [approxValue,iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hh := le_of_tendsto hl (Eventually.of_forall hb)
  unfold curvature gradient
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh

lemma gradient_terminal_small (W : BrownianSystem Ω) (γ : OrderParameter) {D t y : ℝ}
    (hD : 0 ≤ D) (hcap : ∀ s : Time, γ.val s ≤ D) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsmall : 8*kernelConstant*D*Real.sqrt (1-t) ≤ 1/2)
    (hy : |y| ≤ Real.sqrt (1-t)/(4*kernelConstant+2)) :
    |gradient W γ t y| ≤ 1/2 := by
  have hκ := kernelConstant_nonneg
  have hden : 0 < 4*kernelConstant+2 := by positivity
  have hroot := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have hd : Differentiable ℝ (gradient W γ t) := by
    unfold gradient
    simpa only [iteratedDeriv_one] using (value_contDiff W γ ht0 ht1).differentiable_iteratedDeriv 1 (by simp)
  have hL := (lipschitzWith_of_nnnorm_deriv_le hd (C := Real.toNNReal (2*kernelConstant/Real.sqrt (1-t))) (fun x => by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (by positivity)]
    exact curvature_terminal_bound W γ hD hcap ht0 ht1 hsmall x))
  have hh := hL.norm_sub_le y 0
  rw [gradient_zero W γ ht0 ht1,sub_zero,Real.norm_eq_abs,sub_zero,Real.norm_eq_abs,
    Real.coe_toNNReal _ (by positivity)] at hh
  apply hh.trans
  calc
    (2*kernelConstant/Real.sqrt (1-t))*|y| ≤ (2*kernelConstant/Real.sqrt (1-t))*(Real.sqrt (1-t)/(4*kernelConstant+2)) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 2*kernelConstant/(4*kernelConstant+2) := by field_simp
    _ ≤ 1/2 := by apply (div_le_iff₀ hden).mpr;linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.GradientStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma convex_gradient_comparison {f g : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hg : ConvexOn ℝ univ g) (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    {L : ℝ≥0} (hL : LipschitzWith L (deriv g)) {E : ℝ} (hE : ∀ x, |f x-g x| ≤ E)
    {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |deriv f x-deriv g x| ≤ 2*E/h+(L:ℝ)*h := by
  have hfU := hf.deriv_le_slope (mem_univ x) (mem_univ (x+h)) (by linarith) (hfd x)
  have hfL := hf.slope_le_deriv (mem_univ (x-h)) (mem_univ x) (by linarith) (hfd x)
  have hgU := hg.slope_le_deriv (mem_univ x) (mem_univ (x+h)) (by linarith) (hgd (x+h))
  have hgL := hg.deriv_le_slope (mem_univ (x-h)) (mem_univ x) (by linarith) (hgd (x-h))
  have hplus := hL.dist_le_mul (x+h) x
  have hminus := hL.dist_le_mul (x-h) x
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at hplus
  rw [Real.dist_eq,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos hh] at hminus
  have e0 := (abs_le.mp (hE x))
  have e1 := (abs_le.mp (hE (x+h)))
  have e2 := (abs_le.mp (hE (x-h)))
  have hp := abs_le.mp hplus
  have hm := abs_le.mp hminus
  simp only [slope_def_field,add_sub_cancel_left,sub_sub_cancel] at hfU hfL hgU hgL
  have hFU := (le_div_iff₀ hh).mp hfU
  have hFL := (div_le_iff₀ hh).mp hfL
  have hGU := (div_le_iff₀ hh).mp hgU
  have hGL := (le_div_iff₀ hh).mp hgL
  apply abs_le.mpr
  constructor <;> apply (mul_le_mul_iff_right₀ hh).mp
  · have hdiv : (2*E/h)*h=2*E := div_mul_cancel₀ _ hh.ne'
    nlinarith [mul_le_mul_of_nonneg_right hm.1 hh.le]
  · have hdiv : (2*E/h)*h=2*E := div_mul_cancel₀ _ hh.ne'
    nlinarith [mul_le_mul_of_nonneg_right hp.2 hh.le]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_stability (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    ∃ L : ℝ≥0, ∀ β : OrderParameter, ∀ h > 0, ∀ t x,
      |compactGradient W β T t x-compactGradient W γ T t x| ≤
        3*coefficientDistance β γ/h+(L:ℝ)*h := by
  obtain ⟨L,hL⟩ := compactGradient_lipschitz W γ T.property.1 T.property.2
  refine ⟨L,fun β h hh t x => ?_⟩
  have ht0 := (stripClamp_mem T.property.1 t).1
  have ht1 := (stripClamp_mem T.property.1 t).2.trans_lt T.property.2
  have hg : LipschitzWith L (deriv (value W γ (stripClamp T t))) := hL t
  have hb := convex_gradient_comparison (value_convex W β _ ht1.le)
    (value_convex W γ _ ht1.le)
    ((value_contDiff W β ht0 ht1).differentiable (by simp))
    ((value_contDiff W γ ht0 ht1).differentiable (by simp)) hg
    (fun y => value_difference_bound W β γ ht0 ht1.le y) hh x
  change |deriv (value W β (stripClamp T t)) x-deriv (value W γ (stripClamp T t)) x| ≤ _
  convert hb using 1 <;> try rfl
  ring

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.MixedIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma differenceField_generator (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (differenceField W β γ hT0 hT1).generator (compactMixedDrift W β γ T) t x =
      -(1/2:ℝ)*(compactCoeff β T t-compactCoeff γ T t)*(compactGradient W γ T t x)^2 := by
  have hb := (((compactGradient_family W β hT0 hT1).regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hg := (((compactGradient_family W γ hT0 hT1).regular t).smooth.differentiable (by simp) x).hasDerivAt
  change deriv (compactDifference W β γ T t) x*compactMixedDrift W β γ T t x+
    (1/2:ℝ)*deriv (deriv (compactDifference W β γ T t)) x+compactDifferenceRate W β γ T t x=_
  have hd := (hb.sub hg).deriv
  change deriv (fun y => compactGradient W β T t y-compactGradient W γ T t y) x=_ at hd
  rw [compactDifference_deriv W β γ hT0 hT1,hd]
  unfold compactDifferenceRate compactValueRate valueRate compactMixedDrift compactMixedGradient
    compactCoeff compactGradient curvature gradient
  ring

lemma mixedQ_continuous (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    Continuous (mixedQ W β γ T) := by
  convert (mixedStripDrift W β γ T).expected_continuous W
    (compactSquare_family W γ T.property.1 T.property.2)
    (compactSquare_continuous W γ T.property.1 T.property.2) using 1 <;> try rfl
  funext t
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [compactSquare,pow_two]

lemma mixedQ_bounds (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) (t : ℝ) :
    0 ≤ mixedQ W β γ T t ∧ mixedQ W β γ T t ≤ 1 := by
  let := W.isProbability
  have hi : Integrable (fun ξ => (compactGradient W γ T t
      ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ))^2) W.law := by
    simpa only [pow_two,compactSquare] using
      integrable_family_comp (P := W.law) (compactSquare_family W γ T.property.1 T.property.2) t
        ((mixedStripDrift W β γ T).solution_measurable W (Real.toNNReal t))
  refine ⟨integral_nonneg (fun ξ => sq_nonneg _),?_⟩
  calc
    mixedQ W β γ T t ≤ ∫ _ : Ω, (1:ℝ) ∂W.law := integral_mono hi (integrable_const _) (fun ξ => by
      have hh := compactGradient_bound W γ T.property.1 T.property.2 t
        ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal t) ξ)
      rw [abs_le] at hh
      nlinarith)
    _ = 1 := by simp

lemma mixed_difference_right (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time)
    (s : ℝ≥0) (hs : (s:ℝ) < T) :
    HasDerivWithinAt ((differenceField W β γ T.property.1 T.property.2).expected
      (mixedStripDrift W β γ T) W)
      (-(1/2:ℝ)*(compactCoeff β T s-compactCoeff γ T s)*mixedQ W β γ T s) (Ioi (s:ℝ)) s := by
  have hh := (differenceField W β γ T.property.1 T.property.2).expected_hasDerivWithinAt_right
    (mixedStripDrift W β γ T) W s hs (mixedStripDrift_pathDrift_right W β γ T s)
  have he : (∫ ξ, (differenceField W β γ T.property.1 T.property.2).generator
      (mixedStripDrift W β γ T).f s ((mixedStripDrift W β γ T).solution W.driver s ξ) ∂W.law) =
      -(1/2:ℝ)*(compactCoeff β T s-compactCoeff γ T s)*mixedQ W β γ T s := by
    simp only [mixedStripDrift,differenceField_generator,mixedQ,Real.toNNReal_coe]
    rw [integral_const_mul]
  rw [he] at hh
  exact hh

lemma mixed_difference_zero (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    (differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W 0 =
      value W β 0 0-value W γ 0 0 := by
  let := W.isProbability
  have hx (ξ : Ω) : (mixedStripDrift W β γ T).solution W.driver 0 ξ=0 := by
    rw [(mixedStripDrift W β γ T).solution_eq _ W.driver_progressive]
    simp only [NNReal.coe_zero,intervalIntegral.integral_same,W.driver_zero,add_zero]
  simp [TimeField.expected,differenceField,Real.toNNReal_zero,hx,compactDifference,
    stripClamp_eq ⟨le_rfl,T.property.1⟩]

lemma mixed_difference_integral (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    value W β 0 0-value W γ 0 0 =
      (differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W T+
      (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W β γ T s) := by
  let f := (differenceField W β γ T.property.1 T.property.2)
  have hc : ContinuousOn (f.expected (mixedStripDrift W β γ T) W) (Icc (0:ℝ) T) :=
    (f.expected_continuous (mixedStripDrift W β γ T) W).continuousOn
  have hi : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*mixedQ W β γ T s) volume 0 T :=
    ((β.integrable.sub γ.integrable).intervalIntegrable).mul_continuousOn
      (mixedQ_continuous W β γ T).continuousOn
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le T.property.1 hc
    (f' := fun s => -(1/2:ℝ)*((extend β.val s-extend γ.val s)*mixedQ W β γ T s))
    (fun s hs => by
      have hh := mixed_difference_right W β γ T (Real.toNNReal s)
        (by rw [Real.coe_toNNReal _ hs.1.le];exact hs.2)
      simpa only [Real.coe_toNNReal _ hs.1.le,compactCoeff,stripClamp_eq ⟨hs.1.le,hs.2.le⟩,mul_assoc] using hh)
    (hi.const_mul _)
  rw [intervalIntegral.integral_const_mul,mixed_difference_zero] at hh
  dsimp only [f] at hh ⊢
  linarith

lemma mixed_difference_terminal_bound (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) :
    |(differenceField W β γ T.property.1 T.property.2).expected (mixedStripDrift W β γ T) W T| ≤
      (3/2:ℝ)*(∫ s in (T:ℝ)..1, |extend β.val s-extend γ.val s|) := by
  let := W.isProbability
  change |∫ ξ, compactDifference W β γ T T _ ∂W.law| ≤ _
  rw [← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := W.law)
    (f := fun ξ => compactDifference W β γ T T ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal T) ξ))
    (C := (3/2:ℝ)*(∫ s in (T:ℝ)..1, |extend β.val s-extend γ.val s|)) (by
      filter_upwards [] with ξ
      simp only [compactDifference,stripClamp_eq ⟨T.property.1,le_rfl⟩,Real.norm_eq_abs]
      exact value_coefficient_stability W β γ T _ T.property.2.le)
  simpa using hh

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.PerturbationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma perturbationGradientErrors_bddAbove (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    BddAbove (perturbationGradientErrors W γ β T n) := by
  refine ⟨2,?_⟩
  rintro z ⟨p,rfl⟩
  have hb := compactGradient_bound W (perturbation γ β n) T.property.1 T.property.2 p.1 p.2
  have hg := compactGradient_bound W γ T.property.1 T.property.2 p.1 p.2
  exact (abs_sub _ _).trans (by linarith)

lemma perturbationGradientError_nonneg (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    0 ≤ perturbationGradientError W γ β T n :=
  (abs_nonneg _).trans (le_csSup (perturbationGradientErrors_bddAbove W γ β T n) ⟨((0:ℝ),(0:ℝ)),rfl⟩)

lemma perturbationGradientError_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) (t x : ℝ) :
    |compactGradient W (perturbation γ β n) T t x-compactGradient W γ T t x| ≤ perturbationGradientError W γ β T n :=
  le_csSup (perturbationGradientErrors_bddAbove W γ β T n) ⟨(t,x),rfl⟩

lemma perturbationGradientError_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (perturbationGradientError W γ β T) atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := compactGradient_stability W γ T
  rw [Metric.tendsto_nhds]
  intro ε hε
  let h : ℝ := ε/(4*((L:ℝ)+1))
  have hh : 0 < h := by dsimp [h];positivity
  have hLe : (L:ℝ)*h < ε/2 := by
    have hl : 0 < (L:ℝ)+1 := by positivity
    have he : (4*((L:ℝ)+1))*h=ε := by dsimp [h];field_simp
    nlinarith [L.coe_nonneg]
  have hlim : Tendsto (fun n => 3*coefficientDistance (perturbation γ β n) γ/h) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using (tendsto_const_nhds.mul (perturbation_distance_limit γ β) (a := (3:ℝ))).div_const h
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))] with n hn
  have hb : perturbationGradientError W γ β T n ≤ 3*coefficientDistance (perturbation γ β n) γ/h+(L:ℝ)*h := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨p,rfl⟩
    exact hL (perturbation γ β n) h hh p.1 p.2
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (perturbationGradientError_nonneg W γ β T n)]
  linarith

lemma perturbationPathError_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (perturbationPathError W γ β T) atTop (𝓝 0) := by
  unfold perturbationPathError
  have hh := (perturbation_distance_limit γ β).add
    (tendsto_const_nhds.mul (perturbationGradientError_limit W γ β T) (a := γ.val T*(T:ℝ)))
  simpa only [mul_zero,zero_add,zero_mul] using
    (tendsto_const_nhds.mul hh (a := (2:ℝ))).mul_const (Real.exp ((stripDrift W γ T).rate*T))

lemma perturbationPathError_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |(mixedStripDrift W (perturbation γ β n) γ T).solution W.driver t ξ-diffusion W γ t ξ| ≤
      perturbationPathError W γ β T n :=
  mixedPath_error W (perturbation γ β n) γ T (perturbationGradientError_nonneg W γ β T n)
    (perturbationGradientError_bound W γ β T n) t ht ξ

lemma perturbationPath_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    Tendsto (fun n => (mixedStripDrift W (perturbation γ β n) γ T).solution W.driver t ξ)
      atTop (𝓝 (diffusion W γ t ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(perturbationPathError_limit W γ β T).eventually (gt_mem_nhds hε)] with n hn
  exact (perturbationPathError_bound W γ β T n t ht ξ).trans_lt hn

lemma mixedQ_perturbation_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    Tendsto (fun n => mixedQ W (perturbation γ β n) γ T t) atTop
      (𝓝 (squareMoment W γ (diffusion W γ) t)) := by
  let := W.isProbability
  let f (n : ℕ) (ξ : Ω) := (compactGradient W γ T t
    ((mixedStripDrift W (perturbation γ β n) γ T).solution W.driver (Real.toNNReal t) ξ))^2
  have hc : Continuous (compactGradient W γ T t) :=
    (compactGradient_continuous W γ T.property.1 T.property.2).comp (continuous_const.prodMk continuous_id)
  have hm (n : ℕ) : AEStronglyMeasurable (f n) W.law :=
    ((hc.measurable.comp ((mixedStripDrift W (perturbation γ β n) γ T).solution_measurable W (Real.toNNReal t))).pow_const 2).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ ξ ∂W.law, ‖f n ξ‖ ≤ 1 := by
    filter_upwards [] with ξ
    have hh := compactGradient_bound W γ T.property.1 T.property.2 t
      ((mixedStripDrift W (perturbation γ β n) γ T).solution W.driver (Real.toNNReal t) ξ)
    rw [abs_le] at hh
    dsimp only [f]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hl : ∀ᵐ ξ ∂W.law, Tendsto (fun n => f n ξ) atTop
      (𝓝 ((gradient W γ t (diffusion W γ (Real.toNNReal t) ξ))^2)) := by
    filter_upwards [] with ξ
    have hh := (hc.tendsto _).comp (perturbationPath_limit W γ β T (Real.toNNReal t)
      (by rw [Real.coe_toNNReal _ ht.1];exact ht.2) ξ)
    simpa only [Function.comp_apply,f,compactGradient,stripClamp_eq ht] using hh.pow 2
  exact tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) hm (integrable_const _) hb hl

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma squareMoment_bounds (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ} (ht : t ≤ 1) :
    0 ≤ squareMoment W γ (diffusion W γ) t ∧ |squareMoment W γ (diffusion W γ) t| ≤ 1 := by
  let := W.isProbability
  refine ⟨integral_nonneg (fun ξ => sq_nonneg _),?_⟩
  have hb : ∀ᵐ ξ ∂W.law, ‖(gradient W γ t (diffusion W γ (Real.toNNReal t) ξ))^2‖ ≤ 1 := by
    filter_upwards [] with ξ
    have hh := abs_le.mp (gradient_abs_le_one W γ t (diffusion W γ (Real.toNNReal t) ξ) ht)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hh := norm_integral_le_of_norm_le_const hb
  simpa [squareMoment,Real.norm_eq_abs] using hh

lemma squareMoment_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (squareMoment W γ (diffusion W γ)) (Ico (0:ℝ) 1) := by
  intro t ht
  exact (squareMoment_hasDerivWithinAt W γ ht.1 ht.2).continuousWithinAt.mono Ico_subset_Ici_self

lemma curvatureMoment_continuousOn_unit (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (curvatureMoment W γ) (Ico (0:ℝ) 1) := by
  intro t ht
  let T : ℝ := (t+1)/2
  have hT0 : 0 ≤ T := by dsimp [T];linarith [ht.1,ht.2]
  have hT1 : T < 1 := by dsimp [T];linarith [ht.1,ht.2]
  have htt : t < T := by dsimp [T];linarith [ht.1,ht.2]
  have hc := curvatureMoment_continuousOn W γ hT0 hT1 t ⟨ht.1,htt.le⟩
  apply hc.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htt)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma squareMoment_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (squareMoment W γ (diffusion W γ)) (curvatureMoment W γ t) t :=
  (squareMoment_hasDerivWithinAt W γ ht0.le ht1).hasDerivAt (Ici_mem_nhds ht0)

lemma squareMoment_weighted_integrable (W : BrownianSystem Ω) (γ : OrderParameter) {η : ℝ → ℝ}
    (hη : Integrable η) : IntervalIntegrable (fun t => η t*squareMoment W γ (diffusion W γ) t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply hη.integrableOn.mul_bdd
  · exact (squareMoment_continuousOn W γ).aestronglyMeasurable measurableSet_Ico
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact (squareMoment_bounds W γ ht.2.le).2

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.VariationIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma variationTail_limit (γ β : OrderParameter) :
    Tendsto (fun n => variationTail γ β (diffusionHorizon n)) atTop (𝓝 0) := by
  let f := fun s => |extend β.val s-extend γ.val s|
  have hi : Integrable f := (β.integrable.sub γ.integrable).abs
  have he (n : ℕ) : variationTail γ β (diffusionHorizon n)=
      (∫ s in (0:ℝ)..1, f s)-(∫ s in (0:ℝ)..diffusionHorizon n, f s) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := diffusionHorizon n))
      (hi.intervalIntegrable (a := diffusionHorizon n) (b := 1))
    change _ + variationTail γ β (diffusionHorizon n)=_ at hh
    linarith
  have hc := (hi.continuous_primitive 0).tendsto (1:ℝ) |>.comp diffusionHorizon_tendsto
  simpa only [he,sub_self,Function.comp_apply] using tendsto_const_nhds.sub hc (a := ∫ s in (0:ℝ)..1, f s)

lemma mixedQ_weighted_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (fun n => ∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)
      atTop (𝓝 (∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)) := by
  simp only [intervalIntegral.integral_of_le T.property.1]
  apply tendsto_integral_of_dominated_convergence (fun s => |extend β.val s-extend γ.val s|)
  · intro n
    exact ((β.measurable_extend.sub γ.measurable_extend).mul (mixedQ_continuous W (perturbation γ β n) γ T).measurable).aestronglyMeasurable
  · exact (β.integrable.sub γ.integrable).abs.integrableOn
  · intro n
    filter_upwards [] with s
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mixedQ_bounds W (perturbation γ β n) γ T s).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (mixedQ_bounds W (perturbation γ β n) γ T s).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (mixedQ_perturbation_limit W γ β T ⟨hs.1.le,hs.2⟩).const_mul _

lemma normalizedValueDifference_truncation (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    |normalizedValueDifference W γ β n-(1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ),
      (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)| ≤ (3/2:ℝ)*variationTail γ β T := by
  let R := (differenceField W (perturbation γ β n) γ T.property.1 T.property.2).expected
    (mixedStripDrift W (perturbation γ β n) γ T) W T
  let I := ∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s
  have he := mixed_difference_integral W (perturbation γ β n) γ T
  simp only [perturbation_diff,mul_assoc,intervalIntegral.integral_const_mul] at he
  change value W (perturbation γ β n) 0 0-value W γ 0 0=R+(1/2:ℝ)*(variationStep n*I) at he
  have hb := mixed_difference_terminal_bound W (perturbation γ β n) γ T
  simp only [perturbation_diff,abs_mul,abs_of_nonneg (variationStep_pos n).le,intervalIntegral.integral_const_mul] at hb
  change |R| ≤ (3/2:ℝ)*(variationStep n*variationTail γ β T) at hb
  change |normalizedValueDifference W γ β n-(1/2:ℝ)*I| ≤ _
  have hid : normalizedValueDifference W γ β n-(1/2:ℝ)*I=R/variationStep n := by
    unfold normalizedValueDifference
    rw [he]
    field_simp [(variationStep_pos n).ne']
    ring
  rw [hid,abs_div,abs_of_pos (variationStep_pos n)]
  apply (div_le_iff₀ (variationStep_pos n)).mpr
  nlinarith only [hb]

lemma weighted_square_tail_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    |∫ s in (T:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s| ≤ variationTail γ β T := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le T.property.2.le _ ((β.integrable.sub γ.integrable).abs.intervalIntegrable)
  filter_upwards [] with s hs
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (squareMoment_bounds W γ hs.2).2

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma normalizedValueDifference_limit (W : BrownianSystem Ω) (γ β : OrderParameter) :
    Tendsto (normalizedValueDifference W γ β) atTop
      (𝓝 ((1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k,hk⟩ := ((variationTail_limit γ β).eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/8))).exists
  let T := diffusionHorizonTime k
  have htail : variationTail γ β T < ε/8 := hk
  let I (n : ℕ) := (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*mixedQ W (perturbation γ β n) γ T s)
  let J := (1/2:ℝ)*(∫ s in (0:ℝ)..(T:ℝ), (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  let K := (1/2:ℝ)*(∫ s in (T:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  let L := (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)
  have hIL : Tendsto I atTop (𝓝 J) := (mixedQ_weighted_limit W γ β T).const_mul (1/2:ℝ)
  have hi := squareMoment_weighted_integrable W γ (β.integrable.sub γ.integrable)
  have hi0 : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume 0 T :=
    hi.mono_set (by rw [uIcc_of_le T.property.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)];exact Icc_subset_Icc le_rfl T.property.2.le)
  have hi1 : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume T 1 :=
    hi.mono_set (by rw [uIcc_of_le T.property.2.le,uIcc_of_le (by norm_num : (0:ℝ)≤1)];exact Icc_subset_Icc T.property.1 le_rfl)
  have hL : L=J+K := by
    have hh := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    dsimp only [L,J,K]
    rw [← hh,mul_add]
  have hK : |K| ≤ (1/2:ℝ)*variationTail γ β T := by
    dsimp only [K]
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    exact mul_le_mul_of_nonneg_left (weighted_square_tail_bound W γ β T) (by norm_num)
  filter_upwards [(Metric.tendsto_nhds.mp hIL) (ε/2) (by linarith)] with n hn
  change |normalizedValueDifference W γ β n-L| < ε
  have h1 := normalizedValueDifference_truncation W γ β T n
  change |normalizedValueDifference W γ β n-I n| ≤ (3/2:ℝ)*variationTail γ β T at h1
  rw [Real.dist_eq] at hn
  have hh := abs_sub_le (normalizedValueDifference W γ β n) (I n) L
  have hh' := abs_sub_le (I n) J L
  have hJL : |J-L|=|K| := by rw [hL];ring_nf;rw [abs_neg]
  rw [hJL] at hh'
  linarith

lemma penalty_integrable (γ : OrderParameter) :
    IntervalIntegrable (fun s : ℝ => s*extend γ.val s) volume 0 1 := by
  have hh := γ.integrable.intervalIntegrable (a := (0:ℝ)) (b := 1) |>.mul_continuousOn continuousOn_id
  simpa only [id_eq,mul_comm] using hh

lemma penalty_difference (γ β : OrderParameter) (n : ℕ) :
    (∫ s in (0:ℝ)..1, s*extend (perturbation γ β n).val s)-(∫ s in (0:ℝ)..1, s*extend γ.val s)=
      variationStep n*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)) := by
  rw [← intervalIntegral.integral_sub (penalty_integrable _) (penalty_integrable _),← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change s*extend (perturbation γ β n).val s-s*extend γ.val s=variationStep n*(s*(extend β.val s-extend γ.val s))
  rw [← mul_sub,perturbation_diff]
  ring

lemma normalizedParisiDifference_eq (W : BrownianSystem Ω) (γ β : OrderParameter) (n : ℕ) :
    (parisi W (perturbation γ β n)-parisi W γ)/variationStep n=
      normalizedValueDifference W γ β n-(1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)) := by
  have he := penalty_difference γ β n
  have hn := (variationStep_pos n).ne'
  unfold parisi normalizedValueDifference
  field_simp [hn]
  nlinarith only [he]

theorem parisi_chord_derivative (W : BrownianSystem Ω) (γ β : OrderParameter) :
    Tendsto (fun n => (parisi W (perturbation γ β n)-parisi W γ)/variationStep n) atTop
      (𝓝 ((1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s)))) := by
  have hiq := squareMoment_weighted_integrable W γ (β.integrable.sub γ.integrable)
  have hit : IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*s) volume 0 1 :=
    (β.integrable.sub γ.integrable).intervalIntegrable.mul_continuousOn continuousOn_id
  change IntervalIntegrable (fun s => (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s) volume 0 1 at hiq
  have he : (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*squareMoment W γ (diffusion W γ) s)-
      (1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s))=
      (1/2:ℝ)*(∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s)) := by
    rw [← mul_sub,← intervalIntegral.integral_sub hiq (by simpa only [id_eq,mul_comm] using hit)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    ring
  simpa only [normalizedParisiDifference_eq,he] using
    (normalizedValueDifference_limit W γ β).sub_const ((1/2:ℝ)*(∫ s in (0:ℝ)..1, s*(extend β.val s-extend γ.val s)))

theorem minimizer_variational_inequality (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) (β : OrderParameter) :
    0 ≤ ∫ s in (0:ℝ)..1, (extend β.val s-extend γ.val s)*(squareMoment W γ (diffusion W γ) s-s) := by
  have hz := ge_of_tendsto (parisi_chord_derivative W γ β) (Eventually.of_forall (fun n =>
    div_nonneg (sub_nonneg.mpr (hmin (perturbation γ β n))) (variationStep_pos n).le))
  linarith

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.ContactPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma squareMoment_integrable (W : BrownianSystem Ω) (γ : OrderParameter) :
    IntervalIntegrable (squareMoment W γ (diffusion W γ)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply IntegrableOn.of_bound measure_Ico_lt_top ((squareMoment_continuousOn W γ).aestronglyMeasurable measurableSet_Ico) 1
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  simpa only [Real.norm_eq_abs] using (squareMoment_bounds W γ ht.2.le).2

lemma contactIntegrand_integrable (W : BrownianSystem Ω) (γ : OrderParameter) :
    IntervalIntegrable (fun t => squareMoment W γ (diffusion W γ) t-t) volume 0 1 :=
  (squareMoment_integrable W γ).sub (continuous_id.intervalIntegrable 0 1)

lemma contactPotential_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (contactPotential W γ) (Icc (0:ℝ) 1) := by
  have hi : IntegrableOn (fun t => squareMoment W γ (diffusion W γ) t-t) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp (contactIntegrand_integrable W γ)
  unfold contactPotential
  simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using intervalIntegral.continuousOn_primitive_interval_left hi

lemma contactIntegrand_tail_integrable (W : BrownianSystem Ω) (γ : OrderParameter) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun t => squareMoment W γ (diffusion W γ) t-t) volume s 1 := by
  apply (contactIntegrand_integrable W γ).mono_set
  rw [uIcc_of_le hs.2,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Icc_subset_Icc_left hs.1

lemma contactPotential_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {s : ℝ}
    (hs : s ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (contactPotential W γ) (s-squareMoment W γ (diffusion W γ) s) s := by
  have hc : ContinuousOn (fun t => squareMoment W γ (diffusion W γ) t-t) (Ioo (0:ℝ) 1) :=
    ((squareMoment_continuousOn W γ).mono Ioo_subset_Ico_self).sub continuousOn_id
  have hh := intervalIntegral.integral_hasDerivAt_left (contactIntegrand_tail_integrable W γ ⟨hs.1.le,hs.2.le⟩)
    (hc.stronglyMeasurableAtFilter isOpen_Ioo _ hs) (hc.continuousAt (Ioo_mem_nhds hs.1 hs.2))
  unfold contactPotential
  simpa only [neg_sub] using hh

lemma contactPotential_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    (s : Time) : 0 ≤ contactPotential W γ s := by
  have hn := minimizer_variational_inequality W γ hmin (γ.addCDF (Measure.dirac s))
  simp only [OrderParameter.addCDF_difference] at hn
  rw [finiteCDF_fubini (contactIntegrand_integrable W γ),integral_dirac] at hn
  exact hn

lemma contactPotential_remove (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ ν : Measure Time} [IsFiniteMeasure ν] (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) :
    ∫ s : Time, contactPotential W γ s ∂ν ≤ 0 := by
  have hn := minimizer_variational_inequality W γ hmin (γ.removeCDF hμ hν)
  simp only [OrderParameter.removeCDF_difference,neg_mul,intervalIntegral.integral_neg] at hn
  rw [finiteCDF_fubini (contactIntegrand_integrable W γ)] at hn
  change 0 ≤ -(∫ s : Time, contactPotential W γ s ∂ν) at hn
  linarith

lemma contactPotential_compact_mass_removal (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) (K : Set Time) (hK : IsCompact K) :
    ∫ s in K, contactPotential W γ s ∂μ ≤ 0 := by
  let : IsFiniteMeasureOnCompacts μ := (stieltjes_deterministic γ hμ).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ];exact hK.measure_lt_top⟩
  exact contactPotential_remove W γ hmin hμ Measure.restrict_le_self

theorem minimizer_contact (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    ∀ t, SupportDeterministic.InSupport μ t →
      squareMoment W γ (diffusion W γ) t=t ∧ curvatureMoment W γ t ≤ 1 := by
  apply SupportDeterministic.Variation.contact_conditions (stieltjes_deterministic γ hμ)
    ((contactPotential_continuousOn W γ).mono Ico_subset_Icc_self)
  · exact fun t ht => contactPotential_nonneg W γ hmin ⟨t,ht⟩
  · exact contactPotential_compact_mass_removal W γ hmin hμ
  · exact squareMoment_zero W γ
  · intro t ht
    exact (squareMoment_hasDerivWithinAt W γ ht.1 ht.2).mono (Ici_subset_Ici.mpr ht.1)
  · intro t ht
    exact contactPotential_hasDerivAt W γ ht

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma gradientDefect_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ} (ht : t ≤ 1) (x : ℝ) :
    0 ≤ 1-(gradient W γ t x)^2 := by
  have hh := abs_le.mp (gradient_abs_le_one W γ t x ht)
  nlinarith

lemma terminal_plateau_denominator (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s T : Time) (has : a < (s:ℝ)) (hsT : s ≤ T) {x : ℝ} (hx : |x| ≤ 1) :
    varianceHeat ((T:ℝ)-s) (fun y => Real.exp (c*value W γ T y)) x ≤
      Real.exp (c*(value W γ s 0+1)) := by
  rw [varianceHeat_exp_eq_exp_log (value_lipschitz W γ T T.property.2.le),
    ← value_plateau_semigroup W γ hc0 s.property.1 has hsT T.property.2 hc]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hc0
  have hh := (value_lipschitz W γ s s.property.2.le).norm_sub_le x 0
  simp only [Real.norm_eq_abs,NNReal.coe_one,one_mul,sub_zero] at hh
  linarith [le_abs_self (value W γ s x-value W γ s 0)]

lemma terminal_plateau_second_moment_defect (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (ha : a < 1) (hc0 : 0 ≤ c) (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c)
    (s : Time) (hs0 : 0 < (s:ℝ)) (has : a < (s:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Time, ((s:ℝ)+1)/2 ≤ T →
      8*kernelConstant*c*Real.sqrt (1-(T:ℝ)) ≤ 1/2 →
      C*Real.sqrt (1-(T:ℝ)) ≤ 1-squareMoment W γ (diffusion W γ) T := by
  let := W.isProbability
  let δ : ℝ := (1-(s:ℝ))/2
  have hδ : 0 < δ := by dsimp [δ];linarith [s.property.2]
  let M : ℝ := Real.exp (c*(value W γ s 0+1))
  have hM : 0 < M := Real.exp_pos _
  let E : Set Ω := {ξ | diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ ∈ Ioo (-1:ℝ) 1}
  have hmX : Measurable (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0)) :=
    ((diffusion_progressive W γ).adapted _).mono (Filtration.le _ _) le_rfl
  have hE : MeasurableSet E := hmX measurableSet_Ioo
  have hEpos : 0 < W.law.real E := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (diffusion_interval_pos W γ s hs0 (show (-1:ℝ) < 1 by norm_num))
    · exact measure_ne_top _ _
  let K : ℝ := ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ))/(M*(4*kernelConstant+2))
  have hκ := kernelConstant_nonneg
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨W.law.real E*K,mul_pos hEpos hK,fun T hsT hsmall => ?_⟩
  have hst : s ≤ T := by change (s:ℝ) ≤ T;linarith [s.property.2]
  let r : ℝ := Real.sqrt (1-(T:ℝ))/(4*kernelConstant+2)
  have hr0 : 0 ≤ r := by dsimp [r];positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*kernelConstant+2)).mpr
    have hr := Real.sqrt_le_one.mpr (show 1-(T:ℝ) ≤ 1 by linarith [T.property.1])
    linarith
  let g : ℝ → ℝ := fun y => 1-(gradient W γ T y)^2
  have hg := gradientDefect_smooth W γ T.property.1 T.property.2
  have hf := value_regular W γ T.property.1 T.property.2
  have hLip := value_lipschitz W γ T T.property.2.le
  have hg0 : ∀ y, 0 ≤ g y := gradientDefect_nonneg W γ T.property.2.le
  have hgwin : ∀ y, |y| ≤ r → 3/4 ≤ g y := by
    intro y hy
    have hu := abs_le.mp (gradient_terminal_small W γ hc0
      (parameter_bound_of_terminal_plateau γ ha hc) T.property.1 T.property.2 hsmall hy)
    dsimp [g]
    nlinarith
  let F : Ω → ℝ := fun ξ => varianceTilted c ((T:ℝ)-s) (value W γ T) g
    (diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ)
  have hfi : Integrable F W.law := integrable_family_comp (varianceTilted_family hf hLip hg hc0) _ hmX
  have hF0 : ∀ ξ, 0 ≤ F ξ := by
    intro ξ
    dsimp [F]
    rw [varianceTilted_eq_tiltedMean hLip.continuous.measurable hg.smooth.continuous.measurable]
    exact tiltedMean_nonneg hLip hg0 c _ _
  have hlower : ∀ ξ ∈ E, K*Real.sqrt (1-(T:ℝ)) ≤ F ξ := by
    intro ξ hξ
    have hx : |diffusion W γ (⟨s,s.property.1⟩:ℝ≥0) ξ| ≤ 1 := abs_le.mpr ⟨hξ.1.le,hξ.2.le⟩
    have hh := varianceTilted_lower_window hLip hg hc0
      (fun y => (abs_nonneg y).trans (abs_le_value W γ T y T.property.2.le)) hg0 hδ
      (show δ ≤ (T:ℝ)-s by dsimp [δ];linarith)
      (show (T:ℝ)-s ≤ 1 by linarith [T.property.2,s.property.1]) hr0 hr1 hx hgwin
      (terminal_plateau_denominator W γ hc0 hc s T has hst hx)
    have he : ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r)/M=K*Real.sqrt (1-(T:ℝ)) := by
      dsimp [r,K]
      rw [mul_div_assoc,div_div, mul_comm (4*kernelConstant+2) M]
      ring
    rw [he] at hh
    exact hh
  have hint := setIntegral_mono_on (f := fun _ => K*Real.sqrt (1-(T:ℝ)))
    (integrable_const _).integrableOn hfi.integrableOn hE hlower
  rw [setIntegral_const,smul_eq_mul] at hint
  have hb := hint.trans (setIntegral_le_integral hfi (Eventually.of_forall hF0))
  have htrans := terminal_plateau_transition W γ hc0 hc s T has hst hg
  have hiq : Integrable (fun ξ => (gradient W γ T (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ))^2) W.law := by
    have hmT : Measurable (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0)) :=
      ((diffusion_progressive W γ).adapted _).mono (Filtration.le _ _) le_rfl
    have hu := hf.deriv_bounded
    have hsq : BoundedSmooth (fun y => (gradient W γ T y)^2) := by simpa only [gradient,pow_two] using hu.mul hu
    obtain ⟨G,hG⟩ := hsq.bound
    exact Integrable.of_bound (hsq.smooth.continuous.measurable.comp hmT).aestronglyMeasurable G (Eventually.of_forall (fun ξ => hG _))
  have he : (∫ ξ, g (diffusion W γ (⟨T,T.property.1⟩:ℝ≥0) ξ) ∂W.law)=1-squareMoment W γ (diffusion W γ) T := by
    dsimp [g]
    rw [integral_sub (integrable_const _) hiq,integral_const]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,squareMoment]
    congr 2
    funext ξ
    congr 3
    exact (Real.toNNReal_coe (r := (⟨T,T.property.1⟩:ℝ≥0))).symm
  rw [← htrans,he] at hb
  simpa only [mul_assoc] using hb

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Support.NoTerminalPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma terminal_plateau_q_lt_near_one (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc0 : 0 ≤ c)
    (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ t ∈ Ioo b 1, squareMoment W γ (diffusion W γ) t < t := by
  let s₀ : ℝ := (a+1)/2
  have hs0 : 0 < s₀ := by dsimp [s₀];linarith
  have hs1 : s₀ < 1 := by dsimp [s₀];linarith
  have has : a < s₀ := by dsimp [s₀];linarith
  let s : Time := ⟨s₀,⟨hs0.le,hs1⟩⟩
  obtain ⟨C,hC,hbound⟩ := terminal_plateau_second_moment_defect W γ ha1 hc0 hc s hs0 has
  have hl : Tendsto (fun t : ℝ => Real.sqrt (1-t)) (𝓝 1) (𝓝 0) := by
    have hcroot : Continuous (fun t : ℝ => Real.sqrt (1-t)) := by fun_prop
    simpa only [sub_self,Real.sqrt_zero] using hcroot.tendsto (1:ℝ)
  have hm : Tendsto (fun t : ℝ => 8*kernelConstant*c*Real.sqrt (1-t)) (𝓝 1) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hl (a := 8*kernelConstant*c)
  have hev : ∀ᶠ t in 𝓝 (1:ℝ), ((s:ℝ)+1)/2 ≤ t ∧
      8*kernelConstant*c*Real.sqrt (1-t) ≤ 1/2 ∧ Real.sqrt (1-t) < C := by
    filter_upwards [lt_mem_nhds (show ((s:ℝ)+1)/2 < 1 by change (s₀+1)/2 < 1;linarith),
      hm.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num),hl.eventually_lt_const hC] with t ht ht' ht''
    exact ⟨ht.le,ht'.le,ht''⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hev
  let b : ℝ := max 0 (1-ε/2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hb1 : b < 1 := max_lt (by norm_num) (by linarith)
  refine ⟨b,hb0,hb1,fun t ht => ?_⟩
  have hεt : t ∈ Metric.ball (1:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
    dsimp [b] at ht
    linarith [ht.1,le_max_right (0:ℝ) (1-ε/2)]
  obtain ⟨hm0,hm1,hm2⟩ := hball hεt
  have ht0 := hb0.trans ht.1.le
  have hbq := hbound ⟨t,⟨ht0,ht.2⟩⟩ hm0 hm1
  have hroot := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
  have hsqr := Real.sq_sqrt (sub_nonneg.mpr ht.2.le)
  have hmul := mul_lt_mul_of_pos_right hm2 hroot
  change C*Real.sqrt (1-t) ≤ 1-squareMoment W γ (diffusion W γ) t at hbq
  nlinarith

theorem minimizer_no_terminal_plateau (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ) :
    ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧ ∀ t ∈ Ioo a 1, extend γ.val t=c := by
  rintro ⟨a,c,ha0,ha1,hc0,hc⟩
  obtain ⟨b,hb0,hb1,hneg⟩ := terminal_plateau_q_lt_near_one W γ ha0 ha1 hc0 hc
  have hi := (contactIntegrand_tail_integrable W γ ⟨hb0,hb1.le⟩).neg
  have hip : IntegrableOn (fun t => t-squareMoment W γ (diffusion W γ) t) (Ioo b 1) := by
    have hh := (intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).mp hi
    change IntegrableOn (fun t => -(squareMoment W γ (diffusion W γ) t-t)) (Ioo b 1) at hh
    simpa only [neg_sub] using hh
  have hn : 0 ≤ᵐ[volume.restrict (Ioo b 1)] (fun t => t-squareMoment W γ (diffusion W γ) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (hneg t ht).le
  have hsupp : Ioo b 1 ⊆ Function.support (fun t => t-squareMoment W γ (diffusion W γ) t) := by
    intro t ht
    exact ne_of_gt (sub_pos.mpr (hneg t ht))
  have hμpos : 0 < (volume.restrict (Ioo b 1)) (Ioo b 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo,inter_self,Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hb1)
  have hp := (integral_pos_iff_support_of_nonneg_ae hn hip).mpr (hμpos.trans_le (measure_mono hsupp))
  have he : (∫ t in Ioo b 1, t-squareMoment W γ (diffusion W γ) t)=-contactPotential W γ b := by
    unfold contactPotential
    rw [← intervalIntegral.integral_neg]
    simp only [neg_sub]
    rw [intervalIntegral.integral_of_le hb1.le,integral_Ioc_eq_integral_Ioo]
  rw [he] at hp
  linarith [contactPotential_nonneg W γ hmin ⟨b,⟨hb0,hb1⟩⟩]

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem minimizer_full_support_actual (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    μ.support=univ ∧ StrictMonoOn (extend γ.val) (Ico (0:ℝ) 1) ∧
    ∀ t ∈ Ico (0:ℝ) 1, squareMoment W γ (diffusion W γ) t=t ∧ curvatureMoment W γ t=1 := by
  have hh := SupportDeterministic.Variation.full_support_of_contact_and_gap_curvature
    (γ.original_deterministic) (stieltjes_deterministic γ hμ)
    (squareMoment_continuousOn W γ) (curvatureMoment_continuousOn_unit W γ)
    (fun t ht => squareMoment_hasDerivAt W γ ht.1 ht.2) (squareMoment_zero W γ)
    (minimizer_contact W γ hmin hμ) (minimizer_no_terminal_plateau W γ hmin)
    (fun a b c ha hab hb hc hconst => positive_gap_curvature W γ ha hab hb hc hconst)
    (fun a b ha hab hb hconst => zero_gap_curvature W γ ha hab hb hconst)
  have ha := SupportDeterministic.Variation.derivative_eq_one_of_full_contact hh.2.2
    (fun t ht => squareMoment_hasDerivAt W γ ht.1 ht.2)
    (squareMoment_hasDerivWithinAt W γ (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1))
  exact ⟨hh.1,hh.2.1,fun t ht => ⟨hh.2.2 t ht,ha t ht⟩⟩

theorem full_support_oai (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) : FullSupportConclusion W γ := by
  have hμ := parameterMeasure_isStieltjes γ
  have hs := minimizer_full_support_actual W γ hmin hμ
  refine ⟨⟨parameterMeasure γ,hμ⟩,⟨diffusion W γ,diffusion_isDiffusion W γ⟩,
    fun μ hμ => (minimizer_full_support_actual W γ hmin hμ).1,?_,?_⟩
  · intro a b hab
    have hh := hs.2.1 a.property b.property hab
    simpa only [extend,dite_eq_left a.property,dite_eq_left b.property] using hh
  · intro X hX t
    have he : X (Real.toNNReal t)=ᵐ[W.law] diffusion W γ (Real.toNNReal t) := by
      filter_upwards [diffusion_uniqueness W γ hX] with ξ hξ
      apply hξ
      rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ t.property.1,NNReal.coe_one]
      exact t.property.2.le
    have hq : squareMoment W γ X t=squareMoment W γ (diffusion W γ) t := by
      apply integral_congr_ae
      filter_upwards [he] with ξ hξ
      rw [hξ]
    have ha : (∫ ξ, (curvature W γ t (X (Real.toNNReal t) ξ))^2 ∂W.law)=curvatureMoment W γ t := by
      apply integral_congr_ae
      filter_upwards [he] with ξ hξ
      rw [hξ]
    rw [hq,ha]
    exact hs.2.2 t t.property

end ZeroTemperatureSK

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ZeroTemperatureSK.full_support_oai.{u_1} := @OAI.ZeroTemperatureSK.full_support_oai.{u_1}
