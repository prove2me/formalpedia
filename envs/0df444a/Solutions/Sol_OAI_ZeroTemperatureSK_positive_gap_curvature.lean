-- Prove2me | solution 1 for OAI.ZeroTemperatureSK.positive_gap_curvature
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:27.182604+00:00
-- url     : https://prove2.me/submissions/7d608fa7-ef0d-46e0-be4c-25e96d1989eb

import Mathlib
import Definitions.Def_SKFullSupport
import Definitions.Def_OAIQWZT002

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

lemma BoundedSmoothFamily.timeMul {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F)
    {C : ℝ → ℝ} {K : ℝ≥0} (hC : Measurable C) (hb : ∀ t, |C t| ≤ K) :
    BoundedSmoothFamily (fun t x => C t*F t x) :=
  (BoundedSmoothFamily.timeConst hC hb).mul hF

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardGeometry
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

lemma forwardTime_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < forwardTime a t :=
  add_pos_of_pos_of_nonneg ha (le_max_right _ _)

lemma forwardScale_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < forwardScale a t :=
  div_pos ha (forwardTime_pos ha t)

lemma forwardScale_le_one {a : ℝ} (ha : 0 < a) (t : ℝ) : forwardScale a t ≤ 1 := by
  apply (div_le_one (forwardTime_pos ha t)).mpr
  exact le_add_of_nonneg_right (le_max_right _ _)

lemma continuous_forwardTime (a : ℝ) : Continuous (forwardTime a) :=
  continuous_const.add (continuous_id.max continuous_const)
lemma continuous_forwardScale {a : ℝ} (ha : 0 < a) : Continuous (forwardScale a) :=
  continuous_const.div (continuous_forwardTime a) (fun t => ne_of_gt (forwardTime_pos ha t))
lemma continuous_forwardVariance {a : ℝ} (ha : 0 < a) : Continuous (forwardVariance a) :=
  (continuous_const.mul (continuous_id.max continuous_const)).div (continuous_forwardTime a)
    (fun t => ne_of_gt (forwardTime_pos ha t))

lemma hasDerivAt_forwardTime {a t : ℝ} (ht : 0 < t) : HasDerivAt (forwardTime a) 1 t := by
  apply ((hasDerivAt_id t).const_add a).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [forwardTime,max_eq_left (show (0:ℝ) ≤ s from le_of_lt hs),id_eq]

lemma hasDerivAt_forwardScale {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (forwardScale a) (-forwardScale a t/forwardTime a t) t := by
  convert (hasDerivAt_const t a).div (hasDerivAt_forwardTime ht) (ne_of_gt (forwardTime_pos ha t)) using 1 <;>
    first | rfl | (dsimp [forwardScale]; field_simp; ring)

lemma hasDerivAt_forwardVariance {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (forwardVariance a) ((forwardScale a t)^2) t := by
  have he : forwardVariance a = fun s => a-a*forwardScale a s := by
    funext s
    dsimp [forwardVariance,forwardScale]
    field_simp [ne_of_gt (forwardTime_pos ha s)]
    dsimp [forwardTime]
    ring
  rw [he]
  convert ((hasDerivAt_forwardScale ha ht).const_mul a).const_sub a using 1 <;> try rfl
  dsimp [forwardScale]
  field_simp

lemma forwardVariance_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : 0 < forwardVariance a t := by
  exact div_pos (mul_pos ha (lt_of_lt_of_le ht (le_max_left _ _))) (forwardTime_pos ha t)

lemma forwardCorrection_terminal (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ) :
    forwardCorrection a f 0 = f := by
  have he : varianceLogHeat 1 0 f = f := funext (fun x => by
    simpa only [backward,sub_self] using backward_terminal 1 0 f x)
  funext x
  simp only [forwardCorrection,forwardScale,forwardVariance,forwardTime,max_self,add_zero,
    mul_zero,zero_div,div_self ha,Real.log_one,mul_zero,zero_add,one_mul,he]

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.FamilyDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma tendstoUniformlyOn_deriv_family {A : Type*} {S : Set A}
    {f : ℕ → A → ℝ → ℝ} {g : A → ℝ → ℝ}
    (hf : ∀ n, ∀ t ∈ S, ContDiff ℝ 2 (f n t))
    (hg : ∀ t ∈ S, ContDiff ℝ 2 (g t)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ t ∈ S, ∀ x, |deriv (deriv (f n t)) x| ≤ C)
    (hbg : ∀ t ∈ S, ∀ x, |deriv (deriv (g t)) x| ≤ C)
    (hlim : TendstoUniformlyOn (fun n (p : A × ℝ) => f n p.1 p.2)
      (fun p => g p.1 p.2) atTop (S ×ˢ Set.univ)) :
    TendstoUniformlyOn (fun n (p : A × ℝ) => deriv (f n p.1) p.2)
      (fun p => deriv (g p.1) p.2) atTop (S ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  let h : ℝ := ε / (2*C+1)
  have hh : 0 < h := div_pos hε (by positivity)
  filter_upwards [hlim (ε*h/4) (by positivity)] with n hn p hp
  have hA : ∀ x, |(f n p.1-g p.1) x| ≤ ε*h/4 := by
    intro x
    exact le_of_lt (by simpa only [Real.dist_eq,Pi.sub_apply,abs_sub_comm] using hn (p.1,x) ⟨hp.1,mem_univ _⟩)
  have hd (x : ℝ) : deriv (f n p.1-g p.1) x = deriv (f n p.1) x-deriv (g p.1) x :=
    deriv_sub ((hf n p.1 hp.1).differentiable (by norm_num) x)
      ((hg p.1 hp.1).differentiable (by norm_num) x)
  have hdd (x : ℝ) : deriv (deriv (f n p.1-g p.1)) x =
      deriv (deriv (f n p.1)) x-deriv (deriv (g p.1)) x := by
    rw [show deriv (f n p.1-g p.1) = deriv (f n p.1)-deriv (g p.1) from funext hd]
    exact deriv_sub
      (by simpa only [iteratedDeriv_one] using (hf n p.1 hp.1).differentiable_iteratedDeriv 1 (by norm_num) x)
      (by simpa only [iteratedDeriv_one] using (hg p.1 hp.1).differentiable_iteratedDeriv 1 (by norm_num) x)
  have hB : ∀ x, |deriv (deriv (f n p.1-g p.1)) x| ≤ 2*C := by
    intro x
    rw [hdd]
    exact (abs_sub _ _).trans (by linarith [hb n p.1 hp.1 x,hbg p.1 hp.1 x])
  have hi := derivative_interpolation ((hf n p.1 hp.1).sub (hg p.1 hp.1)) hA hB hh p.2
  have hc : h*(2*C) < ε := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*C+1)).mpr
    nlinarith
  have he : 2*(ε*h/4)/h = ε/2 := by field_simp; ring
  change |deriv (f n p.1-g p.1) p.2| ≤ 2*(ε*h/4)/h+h*(2*C)/2 at hi
  rw [he,hd] at hi
  rw [Real.dist_eq,abs_sub_comm]
  linarith

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

lemma gaussianRate_family {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    BoundedSmoothFamily (gaussianRate c f) := by
  have hu := varianceGradient_family hf hLip hc
  convert (hu.deriv.const_mul (1/2:ℝ)).add ((hu.mul hu).const_mul (c/2)) using 1 <;> try rfl
  funext t x
  simp only [gaussianRate,pow_two]

lemma gaussianRate_continuousOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => gaussianRate c f p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  have hu := varianceGradient_continuousOn hf hLip hc T
  have hv := (varianceGradient_family hf hLip hc).continuousOn_iteratedDeriv hu 1
  convert ((continuousOn_const (c := (1/2:ℝ))).mul hv).add
      ((continuousOn_const (c := c/2)).mul (hu.pow 2)) using 1 <;> try rfl
  funext p
  simp only [gaussianRate,iteratedDeriv_one,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]

lemma varianceLogHeat_integral_rate {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, gaussianRate c f t x) = varianceLogHeat c b f x-varianceLogHeat c a f x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · intro t ht
    exact (varianceLogHeat_equation hf hLip c (ha.trans ht.1) x).continuousWithinAt.mono
      (fun s hs => ha.trans hs.1)
  · intro t ht
    exact (varianceLogHeat_equation hf hLip c (ha.trans ht.1.le) x).hasDerivAt
      (Ici_mem_nhds (ha.trans_lt ht.1))
  · exact (gaussianRate_family hf hLip hc).intervalIntegrable x a b

lemma gaussianRate_integral_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv n (gaussianRate c f t) x) =
      iteratedDeriv n (varianceLogHeat c b f) x-iteratedDeriv n (varianceLogHeat c a f) x := by
  have he : (fun z => ∫ t in a..b, gaussianRate c f t z) =
      fun z => varianceLogHeat c b f z-varianceLogHeat c a f z :=
    funext (varianceLogHeat_integral_rate hf hLip hc ha hab)
  have hh := (gaussianRate_family hf hLip hc).iteratedDeriv_integral n a b x
  rw [he,iteratedDeriv_fun_sub (n := n)
    ((regularDatum_varianceLogHeat hf hLip hc b).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((regularDatum_varianceLogHeat hf hLip hc a).smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)] at hh
  exact hh.symm

lemma hasDerivAt_varianceLogHeat_derivative {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (varianceLogHeat c s f) x)
      (iteratedDeriv n (gaussianRate c f t) x) t := by
  have hF := (gaussianRate_family hf hLip hc).iteratedDeriv n
  have hj := (gaussianRate_family hf hLip hc).continuousOn_iteratedDeriv
    (gaussianRate_continuousOn hf hLip hc (t+1)) n
  have hcont : ContinuousAt (fun s => iteratedDeriv n (gaussianRate c f s) x) t := by
    have hh := hj.comp (f := fun s : ℝ => (s,x)) (continuous_id.prodMk continuous_const).continuousOn
      (fun s (hs : s ∈ Icc (0:ℝ) (t+1)) => ⟨hs,mem_univ _⟩)
    exact (hh t ⟨ht.le,by linarith⟩).continuousAt (Icc_mem_nhds ht (by linarith))
  have hi := intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable x 0 t)
    ((hF.measurable.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter) hcont
  apply (hi.const_add (iteratedDeriv n (varianceLogHeat c 0 f) x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [gaussianRate_integral_derivative hf hLip hc le_rfl hs.le n x]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.GaussianValueContinuity
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

lemma varianceLogHeat_time_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c x : ℝ) :
    Continuous (fun t => varianceLogHeat c t f x) := by
  by_cases hc : c=0
  · subst c
    simpa only [varianceLogHeat,↓reduceIte] using
      continuous_varianceHeat hf.smooth.continuous (exponentialBound_of_lipschitz hLip) x
  · change Continuous (fun t => if c=0 then _ else _)
    simp only [hc,↓reduceIte]
    exact ((continuous_varianceHeat (Real.continuous_exp.comp (continuous_const.mul hf.smooth.continuous))
      (exponentialBound_exp hLip c) x).log
      (fun t => ne_of_gt (varianceHeat_exp_pos hLip c t x))).div_const c

lemma varianceLogHeat_joint_continuous {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ × ℝ => varianceLogHeat c p.1 f p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F := fun q : ℝ × ℝ => varianceLogHeat c q.1 f q.2
  have hlim : Tendsto (fun q : ℝ × ℝ => (K:ℝ)*|q.2-p.2|+
      |varianceLogHeat c q.1 f p.2-varianceLogHeat c p.1 f p.2|) (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : ℝ × ℝ => (K:ℝ)*|q.2-p.2|+
        |varianceLogHeat c q.1 f p.2-varianceLogHeat c p.1 f p.2|) := by
      exact (continuous_const.mul (continuous_snd.sub continuous_const).abs).add
        (((varianceLogHeat_time_continuous hf hLip c p.2).comp continuous_fst).sub continuous_const).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hh.continuousAt.tendsto (x := p)
  change Tendsto (fun q : ℝ × ℝ => varianceLogHeat c q.1 f q.2) (𝓝 p) (𝓝 (varianceLogHeat c p.1 f p.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with q hq
  have hb := (varianceLogHeat_lipschitz hLip hc q.1).dist_le_mul q.2 p.2
  have htri := dist_triangle (F q) (varianceLogHeat c q.1 f p.2) (F p)
  simp only [Real.dist_eq] at hb htri ⊢
  exact (htri.trans (add_le_add hb le_rfl)).trans_lt hq

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

lemma forwardCorrection_smooth {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t : ℝ) :
    ContDiff ℝ ∞ (forwardCorrection a f t) := by
  exact contDiff_const.add ((regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) _).smooth.comp
    (contDiff_const.mul contDiff_id))

lemma forwardCorrection_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardCorrection a f t) x = forwardScale a t*
      deriv (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) := by
  have hs := ((regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) (forwardVariance a t)).smooth.differentiable
    (by simp) (forwardScale a t*x)).hasDerivAt
  have hd := (hs.comp x ((hasDerivAt_id x).const_mul (forwardScale a t))).const_add
    ((1/2:ℝ)*Real.log (forwardScale a t))
  convert hd.deriv using 1 <;> first | rfl | ring

lemma forwardGradient_family {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    BoundedSmoothFamily (fun t => deriv (forwardCorrection a f t)) := by
  have hb (t) : |forwardScale a t| ≤ (1:ℝ≥0) := by
    rw [abs_of_pos (forwardScale_pos ha t)]
    exact forwardScale_le_one ha t
  have hh := ((varianceGradient_family hf hLip (by norm_num : (0:ℝ)≤1)).reparam
    (continuous_forwardVariance ha).measurable (continuous_forwardScale ha).measurable hb).timeMul
    (continuous_forwardScale ha).measurable hb
  convert hh using 1 <;> try rfl
  funext t x
  exact forwardCorrection_deriv hf hLip t x

lemma forwardCorrection_regular {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t : ℝ) :
    RegularDatum (forwardCorrection a f t) :=
  ⟨forwardCorrection_smooth hf hLip t,(forwardGradient_family ha hf hLip).regular t⟩

lemma forwardCorrection_jet {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (n : ℕ) (t x : ℝ) :
    iteratedDeriv (n+1) (forwardCorrection a f t) x = (forwardScale a t)^(n+1)*
      iteratedDeriv (n+1) (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) := by
  have hg := (regularDatum_varianceLogHeat hf hLip (by norm_num : (0:ℝ)≤1) (forwardVariance a t)).deriv_bounded.smooth
  have he : deriv (forwardCorrection a f t) = fun x => forwardScale a t*
      deriv (varianceLogHeat 1 (forwardVariance a t) f) (forwardScale a t*x) :=
    funext (forwardCorrection_deriv hf hLip t)
  rw [iteratedDeriv_succ',he,iteratedDeriv_const_mul_field,scaled_composition_jet hg]
  rw [← iteratedDeriv_succ']
  ring

lemma forwardCorrection_continuous {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    Continuous (fun p : ℝ × ℝ => forwardCorrection a f p.1 p.2) := by
  exact (continuous_const.mul (((continuous_forwardScale ha).comp continuous_fst).log
    (fun p => ne_of_gt (forwardScale_pos ha p.1)))).add
    ((varianceLogHeat_joint_continuous hf hLip (by norm_num : (0:ℝ)≤1)).comp
      (((continuous_forwardVariance ha).comp continuous_fst).prodMk
        (((continuous_forwardScale ha).comp continuous_fst).mul continuous_snd)))

lemma forwardGradient_continuous {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    Continuous (fun p : ℝ × ℝ => deriv (forwardCorrection a f p.1) p.2) := by
  obtain ⟨C,hC⟩ := (forwardGradient_family ha hf hLip).deriv.bound
  have hh := continuousOn_deriv_family
    (S := Set.univ) (forwardCorrection_continuous ha hf hLip).continuousOn
    (fun t _ => (forwardCorrection_smooth hf hLip t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) C.coe_nonneg (fun t _ x => hC t x)
  exact continuousOn_univ.mp (by simpa only [univ_prod_univ] using hh)

lemma forwardCorrection_even {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f) (t : ℝ) :
    Function.Even (forwardCorrection a f t) := by
  have heq : varianceLogHeat 1 (forwardVariance a t) f =
      logSemigroup 1 (Real.toNNReal (forwardVariance a t)) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hLip.continuous.measurable 1 _)
  have hEven := logSemigroup_even hf.smooth.continuous.measurable he 1 (Real.toNNReal (forwardVariance a t))
  intro x
  simp only [forwardCorrection,heq,mul_neg]
  rw [hEven]

lemma hasDerivAt_forwardCorrection {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => forwardCorrection a f s x) (forwardCorrectionRate a f t x) t := by
  have hh := hasDerivAt_varianceLogHeat_curve hf hLip 1 (hasDerivAt_forwardVariance ha ht)
    ((hasDerivAt_forwardScale ha ht).mul_const x) (forwardVariance_pos ha ht)
  have hl := ((hasDerivAt_forwardScale ha ht).log (ne_of_gt (forwardScale_pos ha t))).const_mul (1/2:ℝ)
  convert hl.add hh using 1 <;> first | rfl | skip
  rw [forwardCorrectionRate,forwardCorrection_jet hf hLip 1,forwardCorrection_deriv hf hLip]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp [ne_of_gt (forwardTime_pos ha t),ne_of_gt (forwardScale_pos ha t)]
  ring

end ZeroTemperatureSK.Heat

end
end
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

lemma BoundedSmoothFamily.affine {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    AffineSmoothFamily F := by
  refine ⟨F,fun _ _ => 0,hF,hc,BoundedSmoothFamily.timeConst (C := 0) measurable_const
    (fun _ => by simp),continuous_const,?_⟩
  funext t x
  simp

lemma BoundedSmoothFamily.affine_id_mul {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    AffineSmoothFamily (fun t x => x*F t x) := by
  refine ⟨fun _ _ => 0,F,BoundedSmoothFamily.timeConst (C := 0) measurable_const
    (fun _ => by simp),continuous_const,hF,hc,?_⟩
  funext t x
  simp

lemma AffineSmoothFamily.add {F G : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (hG : AffineSmoothFamily G) :
    AffineSmoothFamily (fun t x => F t x+G t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  obtain ⟨C,D,hC,hCc,hD,hDc,rfl⟩ := hG
  refine ⟨fun t x => A t x+C t x,fun t x => B t x+D t x,hA.add hC,hAc.add hCc,
    hB.add hD,hBc.add hDc,?_⟩
  funext t x
  ring

lemma AffineSmoothFamily.const_mul {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (c : ℝ) : AffineSmoothFamily (fun t x => c*F t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  refine ⟨fun t x => c*A t x,fun t x => c*B t x,hA.const_mul c,hAc.const_mul c,
    hB.const_mul c,hBc.const_mul c,?_⟩
  funext t x
  ring

lemma AffineSmoothFamily.continuous {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  exact hAc.add (continuous_snd.mul hBc)

lemma AffineSmoothFamily.smooth {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) (t : ℝ) :
    ContDiff ℝ ∞ (F t) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  exact (hA.regular t).smooth.add (contDiff_id.mul (hB.regular t).smooth)

lemma AffineSmoothFamily.deriv {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    AffineSmoothFamily (fun t => _root_.deriv (F t)) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  have hdA : Continuous (fun p : ℝ × ℝ => _root_.deriv (A p.1) p.2) := by
    simpa only [iteratedDeriv_one] using hA.continuous_iteratedDeriv hAc 1
  have hdB : Continuous (fun p : ℝ × ℝ => _root_.deriv (B p.1) p.2) := by
    simpa only [iteratedDeriv_one] using hB.continuous_iteratedDeriv hBc 1
  refine ⟨fun t x => _root_.deriv (A t) x+B t x,fun t => _root_.deriv (B t),
    hA.deriv.add hB,hdA.add hBc,hB.deriv,hdB,?_⟩
  funext t x
  have hh := ((hA.regular t).smooth.differentiable (by simp) x).hasDerivAt.add
    ((hasDerivAt_id x).mul ((hB.regular t).smooth.differentiable (by simp) x).hasDerivAt)
  convert hh.deriv using 1 <;> first | rfl | (simp only [id_eq];ring)

lemma AffineSmoothFamily.iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (n : ℕ) :
    AffineSmoothFamily (fun t => _root_.iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact hF
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

lemma AffineSmoothFamily.bound {F : ℝ → ℝ → ℝ} (hF : AffineSmoothFamily F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |F t x| ≤ C*(1+|x|) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  obtain ⟨C,hC⟩ := hA.bound
  obtain ⟨D,hD⟩ := hB.bound
  refine ⟨C+D, by positivity,fun t x => ?_⟩
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hh := mul_le_mul_of_nonneg_left (hD t x) (abs_nonneg x)
  nlinarith [hC t x,mul_nonneg C.coe_nonneg (abs_nonneg x)]

lemma AffineSmoothFamily.intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (x a b : ℝ) :
    IntervalIntegrable (fun t => F t x) volume a b :=
  (hF.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _

lemma AffineSmoothFamily.hasDerivAt_integral {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ t in a..b, F t z) (∫ t in a..b, _root_.deriv (F t) x) x := by
  obtain ⟨C,hC,hbound⟩ := hF.deriv.bound
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => F t z) (F' := fun z t => _root_.deriv (F t) z)
    (bound := fun _ => C*(2+|x|)) (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall (fun z => (hF.continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable))
    (hF.intervalIntegrable x a b) ((hF.deriv.continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · filter_upwards [] with t ht z hz
    have hz' : |z-x| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hz
    have habs : |z| ≤ 1+|x| := by
      have hh := abs_add_le (z-x) x
      rw [sub_add_cancel] at hh
      linarith
    exact (hbound t z).trans (by nlinarith)
  · filter_upwards [] with t ht z hz
    exact ((hF.smooth t).differentiable (by simp) z).hasDerivAt

lemma AffineSmoothFamily.iteratedDeriv_integral {F : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (n : ℕ) (a b x : ℝ) :
    _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) x =
      ∫ t in a..b, _root_.iteratedDeriv n (F t) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
    have he : _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) =
        fun z => ∫ t in a..b, _root_.iteratedDeriv n (F t) z := funext hn
    rw [iteratedDeriv_succ,he]
    simpa only [iteratedDeriv_succ] using ((hF.iteratedDeriv n).hasDerivAt_integral a b x).deriv

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

lemma AffineSmoothFamily.mul_bounded {F G : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (hG : BoundedSmoothFamily G)
    (hcG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) :
    AffineSmoothFamily (fun t x => F t x*G t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  refine ⟨fun t x => A t x*G t x,fun t x => B t x*G t x,
    hA.mul hG,hAc.mul hcG,hB.mul hG,hBc.mul hcG,?_⟩
  funext t x
  ring

lemma integral_affine_rate {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, R t x) = F b x-F a x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
  · intro t htt
    exact ht t (ha.trans_lt htt.1) x
  · exact hR.intervalIntegrable x a b

lemma integral_affine_rate_derivative {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (hs : ∀ t, ContDiff ℝ ∞ (F t))
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv n (R t) x) = iteratedDeriv n (F b) x-iteratedDeriv n (F a) x := by
  have he : (fun z => ∫ t in a..b, R t z) = fun z => F b z-F a z :=
    funext (integral_affine_rate hc hR ht ha hab)
  have hh := hR.iteratedDeriv_integral n a b x
  rw [he,iteratedDeriv_fun_sub (n := n)
    ((hs b).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)] at hh
  exact hh.symm

lemma hasDerivAt_affine_evolution_jet {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (hs : ∀ t, ContDiff ℝ ∞ (F t))
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {t : ℝ} (htp : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (F s) x) (iteratedDeriv n (R t) x) t := by
  have hJ := hR.iteratedDeriv n
  have hcont : Continuous (fun s => iteratedDeriv n (R s) x) :=
    hJ.continuous.comp (continuous_id.prodMk continuous_const)
  have hi := intervalIntegral.integral_hasDerivAt_right (hJ.intervalIntegrable x 0 t)
    (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hcont.continuousAt
  apply (hi.const_add (iteratedDeriv n (F 0) x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htp] with s hsp
  rw [integral_affine_rate_derivative hc hR hs ht le_rfl hsp.le n x]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma tiltedMean_add {f g q : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (hq : BoundedSmooth q)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    tiltedMean c h f (fun z => g z+q z) x = tiltedMean c h f g x+tiltedMean c h f q x := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨Q,hQ⟩ := hq.bound
  have hgI := integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c h x
  have hqI := integrable_weight_exp_translate hf hq.smooth.continuous.measurable hQ c h x
  unfold tiltedMean semigroup
  simp_rw [add_mul]
  rw [integral_add hgI hqI,add_div]

lemma tiltedMean_const_mul (f g : ℝ → ℝ) (c d : ℝ) (h : ℝ≥0) (x : ℝ) :
    tiltedMean c h f (fun z => d*g z) x = d*tiltedMean c h f g x := by
  unfold tiltedMean semigroup
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

lemma tiltedMean_const {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c d : ℝ) (h : ℝ≥0) (x : ℝ) : tiltedMean c h f (fun _ => d) x = d := by
  unfold tiltedMean
  have he : semigroup h (fun z => d*Real.exp (c*f z)) x =
      d*semigroup h (fun z => Real.exp (c*f z)) x := integral_const_mul d _
  rw [he]
  exact mul_div_cancel_right₀ d (ne_of_gt (semigroup_exp_pos hf c h x))

lemma tiltedMean_nonneg {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hg : ∀ x, 0 ≤ g x) (c : ℝ) (h : ℝ≥0) (x : ℝ) : 0 ≤ tiltedMean c h f g x := by
  apply div_nonneg _ (semigroup_exp_pos hf c h x).le
  exact integral_nonneg (fun y => mul_nonneg (hg _) (Real.exp_nonneg _))

lemma tiltedMean_pos {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hg : BoundedSmooth g) (hpos : ∀ x, 0 < g x) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 < tiltedMean c h f g x := by
  obtain ⟨G,hG⟩ := hg.bound
  apply div_pos _ (semigroup_exp_pos hf c h x)
  apply (integral_pos_iff_support_of_nonneg (fun y =>
    (mul_pos (hpos (x+y)) (Real.exp_pos _)).le)
    (integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c h x)).mpr
  have he : Function.support (fun y => g (x+y)*Real.exp (c*f (x+y))) = univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (mul_pos (hpos _) (Real.exp_pos _))
  rw [he,measure_univ]
  norm_num

lemma tiltedMean_variance_nonneg {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 ≤ tiltedMean c h f (fun z => (g z)^2) x-(tiltedMean c h f g x)^2 := by
  let m := tiltedMean c h f g x
  have he : (fun z => (g z-m)^2) = fun z => (g z*g z+(-2*m)*g z)+m*m := by
    funext z; ring
  have hh := tiltedMean_nonneg hf (fun z => sq_nonneg (g z-m)) c h x
  rw [he,tiltedMean_add hf ((hg.mul hg).add (hg.const_mul (-2*m))) (BoundedSmooth.const (m*m)),
    tiltedMean_add hf (hg.mul hg) (hg.const_mul (-2*m)),tiltedMean_const_mul,
    tiltedMean_const hf] at hh
  change 0 ≤ tiltedMean c h f (fun z => g z^2) x-m^2
  have hpow : (fun z => g z*g z) = fun z => g z^2 := by funext z; ring
  rw [hpow] at hh
  dsimp only [m] at hh ⊢
  nlinarith

lemma deriv_logSemigroup_tilted {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := by
  funext x
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by funext z; simp [logSemigroup]
    rw [he,(hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).deriv]
    simp [tiltedMean,semigroup]
  · exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip
      (lt_of_le_of_ne hc (Ne.symm hc0)) h x).deriv

lemma logSemigroup_curvature_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hpos : ∀ x, 0 < deriv (deriv f) x)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    0 < deriv (deriv (logSemigroup c h f)) x := by
  rw [deriv_logSemigroup_tilted hf hLip hc,
    (hasDerivAt_tiltedMean hf hLip hf.deriv_bounded hc h x).deriv]
  have he : (fun z => deriv (deriv f) z+c*deriv f z*deriv f z) =
      fun z => deriv (deriv f) z+c*(deriv f z*deriv f z) := by funext z; ring
  rw [he,tiltedMean_add hLip hf.deriv_bounded.deriv
    ((hf.deriv_bounded.mul hf.deriv_bounded).const_mul c),tiltedMean_const_mul]
  have hp := tiltedMean_pos hLip hf.deriv_bounded.deriv hpos c h x
  have hv := mul_nonneg hc (tiltedMean_variance_nonneg hLip hf.deriv_bounded c h x)
  have hpow : (fun z => deriv f z*deriv f z) = fun z => (deriv f z)^2 := by funext z; ring
  rw [hpow]
  nlinarith

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.BurgersConstruction
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

lemma hasDerivAt_spatialJet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  simpa only [iteratedDeriv_succ] using
    ((contDiff_iteratedDeriv_infty hf n).differentiable (by simp) x).hasDerivAt

lemma gaussianBurgers_jet {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (n : ℕ) (t x : ℝ) : iteratedDeriv n (gaussianBurgers c f t) x =
      c*iteratedDeriv (n+1) (varianceLogHeat c t f) x := by
  change iteratedDeriv n (fun x => c*deriv (varianceLogHeat c t f) x) x = _
  rw [iteratedDeriv_const_mul c
    ((regularDatum_varianceLogHeat hf hLip hc t).deriv_bounded.smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),iteratedDeriv_succ']

lemma gaussianBurgers_rate {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (t : ℝ) : burgersRate (gaussianBurgers c f) t = fun x => c*deriv (gaussianRate c f t) x := by
  have hG := (regularDatum_varianceLogHeat hf hLip hc t).smooth
  funext x
  have h₁ := hasDerivAt_spatialJet hG 1 x
  have h₂ := hasDerivAt_spatialJet hG 2 x
  have hd : HasDerivAt (gaussianRate c f t)
      ((1/2:ℝ)*iteratedDeriv 3 (varianceLogHeat c t f) x+
        c*deriv (varianceLogHeat c t f) x*iteratedDeriv 2 (varianceLogHeat c t f) x) x := by
    convert (h₂.const_mul (1/2:ℝ)).add ((h₁.pow 2).const_mul (c/2)) using 1 <;>
      first | rfl | ((try funext y); simp only [gaussianRate, Pi.add_apply, Pi.pow_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  rw [hd.deriv,burgersRate,gaussianBurgers_jet hf hLip hc 2]
  have he := gaussianBurgers_jet hf hLip hc 1 t x
  simp only [iteratedDeriv_one] at he
  rw [he]
  dsimp only [gaussianBurgers]
  ring

theorem gaussianBurgers_smooth {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) :
    SmoothBurgers (gaussianBurgers c f) := by
  refine ⟨(varianceGradient_family hf hLip hc).const_mul c,?_,?_⟩
  · intro T
    exact continuousOn_const.mul (varianceGradient_continuousOn hf hLip hc T)
  · intro n t ht x
    have he : (fun s => iteratedDeriv n (gaussianBurgers c f s) x) =
        fun s => c*iteratedDeriv (n+1) (varianceLogHeat c s f) x :=
      funext (fun s => gaussianBurgers_jet hf hLip hc n s x)
    rw [he,gaussianBurgers_rate hf hLip hc,
      iteratedDeriv_const_mul c (((gaussianRate_family hf hLip hc).deriv.regular t).smooth.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),← iteratedDeriv_succ']
    exact (hasDerivAt_varianceLogHeat_derivative hf hLip hc ht (n+1) x).const_mul c

lemma even_deriv_odd {f : ℝ → ℝ} (hf : Differentiable ℝ f) (he : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have hh := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have heq : (fun y => f (-y)) = f := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hh
  rw [heq] at hh
  linarith [hh.deriv]

lemma odd_deriv_even {f : ℝ → ℝ} (hf : Differentiable ℝ f) (he : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have hh := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have heq : (fun y => f (-y)) = fun y => -f y := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hh
  rw [heq] at hh
  have hder := (hf x).hasDerivAt.neg
  have he' := hh.unique hder
  linarith

lemma gaussianBurgers_odd {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : Function.Odd (gaussianBurgers c f t) := by
  have heq : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  have hodd := even_deriv_odd ((regularDatum_varianceLogHeat hf hLip hc t).smooth.differentiable (by simp))
    (by rw [heq]; exact logSemigroup_even hf.smooth.continuous.measurable he _ _)
  intro x
  simp only [gaussianBurgers,hodd x,mul_neg]

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma inverse_forwardTime_family {a : ℝ} (ha : 0 < a) :
    BoundedSmoothFamily (fun t (_x : ℝ) => (forwardTime a t)⁻¹) := by
  apply BoundedSmoothFamily.timeConst (C := Real.toNNReal a⁻¹)
    (continuous_forwardTime a).measurable.inv
  intro t
  change |(forwardTime a t)⁻¹| ≤ (Real.toNNReal a⁻¹ : ℝ)
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr ha.le),abs_of_pos (inv_pos.mpr (forwardTime_pos ha t))]
  exact inv_anti₀ ha (le_add_of_nonneg_right (le_max_right _ _))

lemma inverse_forwardTime_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (fun t => (forwardTime a t)⁻¹) :=
  (continuous_forwardTime a).inv₀ (fun t => ne_of_gt (forwardTime_pos ha t))

lemma forwardCorrectionRate_affine {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    AffineSmoothFamily (forwardCorrectionRate a f) := by
  have hU := forwardGradient_family ha hf hLip
  have hUc := forwardGradient_continuous ha hf hLip
  have hUx : Continuous (fun p : ℝ × ℝ => deriv (deriv (forwardCorrection a f p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using hU.continuous_iteratedDeriv hUc 1
  have hI := inverse_forwardTime_family ha
  have hIc : Continuous (fun p : ℝ × ℝ => (forwardTime a p.1)⁻¹) :=
    (inverse_forwardTime_continuous ha).comp continuous_fst
  let A (t x : ℝ) := (1/2:ℝ)*deriv (deriv (forwardCorrection a f t)) x+
    (1/2:ℝ)*(deriv (forwardCorrection a f t) x)^2-(1/2:ℝ)*(forwardTime a t)⁻¹
  let B (t x : ℝ) := -(forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x
  refine ⟨A,B,?_,?_,?_,?_,?_⟩
  · convert ((hU.deriv.const_mul (1/2:ℝ)).add ((hU.mul hU).const_mul (1/2:ℝ))).add
      (hI.const_mul (-1/2:ℝ)) using 1 <;> try rfl
    funext t x
    dsimp [A]
    ring
  · dsimp [A]
    exact ((hUx.const_mul (1/2:ℝ)).add ((hUc.pow 2).const_mul (1/2:ℝ))).sub (hIc.const_mul (1/2:ℝ))
  · convert (hI.const_mul (-1)).mul hU using 1 <;> try rfl
    simp only [neg_one_mul]
    rfl
  · exact hIc.neg.mul hUc
  · funext t x
    dsimp [A,B,forwardCorrectionRate]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv]
    ring

lemma hasDerivAt_forwardCorrection_jet {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (forwardCorrection a f s) x)
      (iteratedDeriv n (forwardCorrectionRate a f t) x) t :=
  hasDerivAt_affine_evolution_jet (forwardCorrection_continuous ha hf hLip)
    (forwardCorrectionRate_affine ha hf hLip) (forwardCorrection_smooth hf hLip)
    (fun _ htt x => hasDerivAt_forwardCorrection ha hf hLip htt x) ht n x

lemma forwardScore_affine {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) : AffineSmoothFamily (forwardScore a f) := by
  have hI := inverse_forwardTime_family ha
  have hIc : Continuous (fun p : ℝ × ℝ => (forwardTime a p.1)⁻¹) :=
    (inverse_forwardTime_continuous ha).comp continuous_fst
  have hU := forwardGradient_family ha hf hLip
  have hUc := forwardGradient_continuous ha hf hLip
  convert (hI.affine_id_mul hIc).add ((hU.affine hUc).const_mul (-1)) using 1 <;> try rfl
  funext t x
  simp only [forwardScore,div_eq_mul_inv,neg_one_mul,sub_eq_add_neg]

lemma forwardScore_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardScore a f t) x=(forwardTime a t)⁻¹-iteratedDeriv 2 (forwardCorrection a f t) x := by
  have hh := ((hasDerivAt_id x).div_const (forwardTime a t)).sub
    (hasDerivAt_spatialJet (forwardCorrection_smooth (a := a) hf hLip t) 1 x)
  convert hh.deriv using 1 <;> first | rfl | (simp only [one_div,iteratedDeriv_one] <;> rfl)

lemma forwardScore_deriv_family {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) :
    BoundedSmoothFamily (fun t => deriv (forwardScore a f t)) := by
  convert (inverse_forwardTime_family ha).add ((forwardGradient_family ha hf hLip).deriv.const_mul (-1)) using 1 <;> try rfl
  funext t x
  rw [forwardScore_deriv hf hLip]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,neg_one_mul,sub_eq_add_neg]

lemma forwardScore_second {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    iteratedDeriv 2 (forwardScore a f t) x = -iteratedDeriv 3 (forwardCorrection a f t) x := by
  have he : deriv (forwardScore a f t) = fun x =>
      (forwardTime a t)⁻¹-iteratedDeriv 2 (forwardCorrection a f t) x := funext (forwardScore_deriv hf hLip t)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  exact ((hasDerivAt_spatialJet (forwardCorrection_smooth (a := a) hf hLip t) 2 x).const_sub _).deriv

lemma forwardCorrectionRate_deriv {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (t x : ℝ) :
    deriv (forwardCorrectionRate a f t) x =
      (1/2:ℝ)*iteratedDeriv 3 (forwardCorrection a f t) x+
      deriv (forwardCorrection a f t) x*iteratedDeriv 2 (forwardCorrection a f t) x-
      ((forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x+
        x/forwardTime a t*iteratedDeriv 2 (forwardCorrection a f t) x) := by
  have hL := forwardCorrection_smooth (a := a) hf hLip t
  have hh := ((((hasDerivAt_spatialJet hL 2 x).const_mul (1/2:ℝ)).add
    (((hasDerivAt_spatialJet hL 1 x).pow 2).const_mul (1/2:ℝ))).sub
    (((hasDerivAt_id x).div_const (forwardTime a t)).mul (hasDerivAt_spatialJet hL 1 x))).sub_const
    ((1/2:ℝ)/forwardTime a t)
  have hh' : HasDerivAt (forwardCorrectionRate a f t)
      ((1/2:ℝ)*iteratedDeriv 3 (forwardCorrection a f t) x+
      deriv (forwardCorrection a f t) x*iteratedDeriv 2 (forwardCorrection a f t) x-
      ((forwardTime a t)⁻¹*deriv (forwardCorrection a f t) x+
        x/forwardTime a t*iteratedDeriv 2 (forwardCorrection a f t) x)) x := by
    convert hh using 1 <;> first | rfl | ((try funext y); simp only [forwardCorrectionRate,iteratedDeriv_one,id_eq,one_div,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply] <;> ring)
  exact hh'.deriv

lemma hasDerivAt_forwardScore {a t : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u => forwardScore a f u x) (scoreRate (forwardScore a f) t x) t := by
  have hd := ((hasDerivAt_const t x).div (hasDerivAt_forwardTime ht)
    (ne_of_gt (forwardTime_pos ha t))).sub (hasDerivAt_forwardCorrection_jet ha hf hLip ht 1 x)
  convert hd using 1 <;> try rfl
  · funext u
    simp only [forwardScore,iteratedDeriv_one,Pi.sub_apply,Pi.div_apply]
  simp only [iteratedDeriv_one]
  rw [forwardCorrectionRate_deriv hf hLip, scoreRate,forwardScore_second hf hLip,forwardScore_deriv hf hLip]
  dsimp only [forwardScore]
  field_simp [ne_of_gt (forwardTime_pos ha t)]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.BurgersJets
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

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma jet_spatial (n : ℕ) (t x : ℝ) :
    HasDerivAt (iteratedDeriv n (r t)) (iteratedDeriv (n+1) (r t) x) x :=
  hasDerivAt_spatialJet (hr.family.regular t).smooth n x

lemma jet_continuous (n : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (r p.1) p.2) (Icc (0:ℝ) T ×ˢ univ) :=
  hr.family.continuousOn_iteratedDeriv (hr.continuous T) n

lemma rate_family : BoundedSmoothFamily (burgersRate r) := by
  convert (hr.family.deriv.deriv.const_mul (1/2:ℝ)).add (hr.family.mul hr.family.deriv) using 1 <;> try rfl
  funext t x
  simp only [burgersRate,iteratedDeriv_succ,iteratedDeriv_zero]

lemma rate_continuous (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => burgersRate r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  exact (continuousOn_const.mul (hr.jet_continuous 2 T)).add
    ((hr.continuous T).mul (by simpa only [iteratedDeriv_one] using hr.jet_continuous 1 T))

lemma rate_deriv (t x : ℝ) :
    deriv (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x := by
  have hd := ((hr.jet_spatial 2 t x).const_mul (1/2:ℝ)).add
    ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 1 t x))
  have hd' : HasDerivAt (burgersRate r t) ((1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma rate_jet2 (t x : ℝ) :
    iteratedDeriv 2 (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 4 (r t) x+
      3*deriv (r t) x*iteratedDeriv 2 (r t) x+r t x*iteratedDeriv 3 (r t) x := by
  have he : deriv (burgersRate r t) = fun y => (1/2:ℝ)*iteratedDeriv 3 (r t) y+
      (deriv (r t) y)^2+r t y*iteratedDeriv 2 (r t) y := funext (hr.rate_deriv t)
  have hd := (((hr.jet_spatial 3 t x).const_mul (1/2:ℝ)).add
    ((hr.jet_spatial 1 t x).pow 2)).add ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 2 t x))
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert hd.deriv using 1 <;> first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; first | rfl | ring)

lemma rate_jet3 (t x : ℝ) :
    iteratedDeriv 3 (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 5 (r t) x+
      3*(iteratedDeriv 2 (r t) x)^2+4*deriv (r t) x*iteratedDeriv 3 (r t) x+
      r t x*iteratedDeriv 4 (r t) x := by
  have he : iteratedDeriv 2 (burgersRate r t) = fun y => (1/2:ℝ)*iteratedDeriv 4 (r t) y+
      3*deriv (r t) y*iteratedDeriv 2 (r t) y+r t y*iteratedDeriv 3 (r t) y := funext (hr.rate_jet2 t)
  have hd := (((hr.jet_spatial 4 t x).const_mul (1/2:ℝ)).add
    (((hr.jet_spatial 1 t x).const_mul 3).mul (hr.jet_spatial 2 t x))).add
    ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 3 t x))
  rw [iteratedDeriv_succ (n := 2),he]
  convert hd.deriv using 1 <;> first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; first | rfl | ring)

lemma rate_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => burgersRate r s x)
      ((1/2:ℝ)*iteratedDeriv 2 (burgersRate r t) x+
        r t x*deriv (burgersRate r t) x+deriv (r t) x*burgersRate r t x) t := by
  convert ((hr.time_derivative 2 t ht x).const_mul (1/2:ℝ)).add
    ((hr.time_derivative 0 t ht x).mul (hr.time_derivative 1 t ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma rate_deriv_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => deriv (burgersRate r s) x)
      ((1/2:ℝ)*iteratedDeriv 3 (burgersRate r t) x+
        2*deriv (r t) x*deriv (burgersRate r t) x+
        burgersRate r t x*iteratedDeriv 2 (r t) x+
        r t x*iteratedDeriv 2 (burgersRate r t) x) t := by
  have he : (fun s => deriv (burgersRate r s) x) = fun s =>
      (1/2:ℝ)*iteratedDeriv 3 (r s) x+(deriv (r s) x)^2+r s x*iteratedDeriv 2 (r s) x :=
    funext (fun s => hr.rate_deriv s x)
  rw [he]
  convert (((hr.time_derivative 3 t ht x).const_mul (1/2:ℝ)).add
    ((hr.time_derivative 1 t ht x).pow 2)).add
    ((hr.time_derivative 0 t ht x).mul (hr.time_derivative 2 t ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma rate_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) : Function.Odd (burgersRate r t) := by
  have he := odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)
  have hw := even_deriv_odd ((hr.family.deriv.regular t).smooth.differentiable (by simp)) he
  intro x
  simp only [burgersRate,iteratedDeriv_succ,iteratedDeriv_zero,hw x,he x,ho t x]
  ring

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma wronskian_family : BoundedSmoothFamily (backwardWronskian r) := by
  convert (hr.family.mul hr.rate_family.deriv).add
    ((hr.family.deriv.mul hr.rate_family).const_mul (-1)) using 1 <;> try rfl
  funext t x
  simp only [backwardWronskian]
  ring

lemma wronskian_continuous (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => backwardWronskian r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  apply ContinuousOn.sub
  · exact (hr.continuous T).mul (by simpa only [iteratedDeriv_one] using
      hr.rate_family.continuousOn_iteratedDeriv (hr.rate_continuous T) 1)
  · have hv : ContinuousOn (fun p : ℝ × ℝ => deriv (r p.1) p.2) (Icc (0:ℝ) T ×ˢ univ) := by
      simpa only [iteratedDeriv_one] using hr.jet_continuous 1 T
    exact hv.mul (hr.rate_continuous T)

lemma wronskian_deriv (t x : ℝ) :
    deriv (backwardWronskian r t) x =
      r t x*iteratedDeriv 2 (burgersRate r t) x-iteratedDeriv 2 (r t) x*burgersRate r t x := by
  have hp (n) := hasDerivAt_spatialJet (hr.rate_family.regular t).smooth n x
  have hd := ((hr.jet_spatial 0 t x).mul (hp 1)).sub ((hr.jet_spatial 1 t x).mul (hp 0))
  have hd' : HasDerivAt (backwardWronskian r t)
      (r t x*iteratedDeriv 2 (burgersRate r t) x-iteratedDeriv 2 (r t) x*burgersRate r t x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [backwardWronskian,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma wronskian_jet2 (t x : ℝ) :
    iteratedDeriv 2 (backwardWronskian r t) x =
      deriv (r t) x*iteratedDeriv 2 (burgersRate r t) x+
      r t x*iteratedDeriv 3 (burgersRate r t) x-
      (iteratedDeriv 3 (r t) x*burgersRate r t x+
        iteratedDeriv 2 (r t) x*deriv (burgersRate r t) x) := by
  have hp (n) := hasDerivAt_spatialJet (hr.rate_family.regular t).smooth n x
  have he : deriv (backwardWronskian r t) = fun y =>
      r t y*iteratedDeriv 2 (burgersRate r t) y-iteratedDeriv 2 (r t) y*burgersRate r t y :=
    funext (hr.wronskian_deriv t)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert (((hr.jet_spatial 0 t x).mul (hp 2)).sub ((hr.jet_spatial 2 t x).mul (hp 0))).deriv
    using 1 <;> first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]

lemma wronskian_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => backwardWronskian r s x) (wronskianRate r t x) t := by
  convert ((hr.time_derivative 0 t ht x).mul (hr.rate_deriv_time ht x)).sub
    ((hr.time_derivative 1 t ht x).mul (hr.rate_time ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [backwardWronskian,wronskianRate,
      Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero])

lemma wronskian_equation (t x : ℝ) (hne : r t x ≠ 0) :
    wronskianRate r t x-(1/2:ℝ)*iteratedDeriv 2 (backwardWronskian r t) x-
      (r t x-deriv (r t) x/r t x)*deriv (backwardWronskian r t) x-
      2*(burgersRate r t x/r t x)*backwardWronskian r t x =
        r t x*iteratedDeriv 2 (r t) x*burgersRate r t x := by
  rw [hr.wronskian_jet2,hr.wronskian_deriv]
  simp only [wronskianRate,backwardWronskian,hr.rate_deriv,hr.rate_jet2,hr.rate_jet3,burgersRate]
  field_simp [hne]
  ring

lemma wronskian_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) :
    Function.Odd (backwardWronskian r t) := by
  have hr' := odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)
  have hp := hr.rate_odd ho t
  have hp' := odd_deriv_even ((hr.rate_family.regular t).smooth.differentiable (by simp)) hp
  intro x
  simp only [backwardWronskian,ho t x,hr' x,hp x,hp' x]
  ring

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardConstruction
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

lemma scoreRate_affine {s : ℝ → ℝ → ℝ} (hs : AffineSmoothFamily s)
    (hds : BoundedSmoothFamily (fun t => deriv (s t))) : AffineSmoothFamily (scoreRate s) := by
  have hc := hs.deriv.continuous
  have h₂c := hs.deriv.deriv.continuous
  convert ((hds.deriv.affine h₂c).const_mul (1/2:ℝ)).add
    ((hs.mul_bounded hds hc).const_mul (-1)) using 1 <;> try rfl
  funext t x
  simp only [scoreRate,iteratedDeriv_succ,iteratedDeriv_zero,neg_one_mul,sub_eq_add_neg]

theorem forwardScore_smooth {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) : SmoothForward (forwardScore a f) := by
  have hs := forwardScore_affine ha hf hLip
  have hds := forwardScore_deriv_family ha hf hLip
  refine ⟨hs,hds,fun n t ht x => ?_⟩
  exact hasDerivAt_affine_evolution_jet hs.continuous (scoreRate_affine hs hds) hs.smooth
    (fun t htt x => hasDerivAt_forwardScore ha hf hLip htt x) ht n x

namespace SmoothForward
variable {s : ℝ → ℝ → ℝ} (hs : SmoothForward s)
include hs

lemma jet_spatial (n : ℕ) (t x : ℝ) :
    HasDerivAt (iteratedDeriv n (s t)) (iteratedDeriv (n+1) (s t) x) x :=
  hasDerivAt_spatialJet (hs.family.smooth t) n x

lemma jet_continuous (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (s p.1) p.2) :=
  (hs.family.iteratedDeriv n).continuous

lemma jet_family (n : ℕ) : BoundedSmoothFamily (fun t => iteratedDeriv (n+1) (s t)) := by
  simpa only [iteratedDeriv_succ'] using hs.deriv_family.iteratedDeriv n

lemma rate_deriv (t x : ℝ) : deriv (scoreRate s t) x =
    (1/2:ℝ)*iteratedDeriv 3 (s t) x-(deriv (s t) x)^2-s t x*iteratedDeriv 2 (s t) x := by
  have hd := ((hs.jet_spatial 2 t x).const_mul (1/2:ℝ)).sub
    ((hs.jet_spatial 0 t x).mul (hs.jet_spatial 1 t x))
  have hd' : HasDerivAt (scoreRate s t) ((1/2:ℝ)*iteratedDeriv 3 (s t) x-
      (deriv (s t) x)^2-s t x*iteratedDeriv 2 (s t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only [scoreRate,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma rate_jet2 (t x : ℝ) : iteratedDeriv 2 (scoreRate s t) x =
    (1/2:ℝ)*iteratedDeriv 4 (s t) x-3*deriv (s t) x*iteratedDeriv 2 (s t) x-
      s t x*iteratedDeriv 3 (s t) x := by
  have he : deriv (scoreRate s t) = fun y => (1/2:ℝ)*iteratedDeriv 3 (s t) y-
      (deriv (s t) y)^2-s t y*iteratedDeriv 2 (s t) y := funext (hs.rate_deriv t)
  have hd := (((hs.jet_spatial 3 t x).const_mul (1/2:ℝ)).sub
    ((hs.jet_spatial 1 t x).pow 2)).sub ((hs.jet_spatial 0 t x).mul (hs.jet_spatial 2 t x))
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  apply HasDerivAt.deriv
  convert hd using 1 <;> first | rfl | ((try funext y); simp only [iteratedDeriv_succ,iteratedDeriv_zero,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply] <;> ring)

lemma second_odd (ho : ∀ t, Function.Odd (s t)) (t : ℝ) :
    Function.Odd (iteratedDeriv 2 (s t)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
   (even_deriv_odd ((hs.deriv_family.regular t).smooth.differentiable (by simp))
    (odd_deriv_even ((hs.family.smooth t).differentiable (by simp)) (ho t)))

end SmoothForward

lemma forwardScore_odd {a : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f) (t : ℝ) :
    Function.Odd (forwardScore a f t) := by
  have hd := even_deriv_odd ((forwardCorrection_smooth (a := a) hf hLip t).differentiable (by simp))
    (forwardCorrection_even hf hLip he t)
  intro x
  simp only [forwardScore,neg_div,hd x]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open Set Filter
open scoped Topology

namespace ZeroTemperatureSK.Parabolic

theorem second_derivative_nonnegative_at_min {f : ℝ → ℝ} {x d₂ : ℝ}
    (hf : Continuous f) (hm : IsLocalMin f x)
    (hd₂ : HasDerivAt (deriv f) d₂ x) : 0 ≤ d₂ := by
  by_contra hn
  have hneg : d₂ < 0 := lt_of_not_ge hn
  have hzero : deriv f x = 0 := hm.deriv_eq_zero
  have hr := (hasDerivAt_iff_tendsto_slope_left_right.mp hd₂).2
  have he : ∀ᶠ y in 𝓝[>] x, deriv f y < 0 := by
    filter_upwards [hr.eventually (Iio_mem_nhds hneg), self_mem_nhdsWithin] with y hy hxy
    have hpos : 0 < y-x := sub_pos.mpr hxy
    simpa only [slope_def_field, hzero, sub_zero, div_lt_iff₀ hpos, zero_mul] using hy
  have he' : ∀ᶠ y in 𝓝[>] x, deriv f y < 0 ∧ f x ≤ f y :=
    he.and (hm.filter_mono nhdsWithin_le_nhds)
  obtain ⟨b, hxb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he'
  obtain ⟨y, hxy, hyb⟩ := exists_between (show x < b from hxb)
  have hanti : StrictAntiOn f (Icc x y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x y) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    exact (hb ⟨ht.1, ht.2.trans hyb⟩).1
  have hlt := hanti (left_mem_Icc.mpr hxy.le) (right_mem_Icc.mpr hxy.le) hxy
  exact (not_lt_of_ge (hb ⟨hxy, hyb⟩).2) hlt

theorem time_derivative_nonpositive {f : ℝ → ℝ} {a b x d : ℝ}
    (hax : a < x) (hxb : x ≤ b)
    (hd : HasDerivWithinAt f d (Icc a b) x)
    (hm : IsMinOn f (Icc a b) x) : d ≤ 0 := by
  have hd' : HasDerivWithinAt f d (Icc a x) x :=
    hd.mono (Icc_subset_Icc_right hxb)
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd'
  have hset : Icc a x \ {x} = Ico a x := by
    ext y
    simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ico]
    constructor
    · rintro ⟨⟨hay, hyx⟩, hne⟩
      exact ⟨hay, lt_of_le_of_ne hyx hne⟩
    · rintro ⟨hay, hyx⟩
      exact ⟨⟨hay, hyx.le⟩, hyx.ne⟩
  rw [hset, nhdsWithin_Ico_eq_nhdsLT hax] at hs
  apply le_of_tendsto hs
  have hmem : ∀ᶠ y in 𝓝[<] x, y ∈ Ico a x := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hax]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with y hy
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr (hm ⟨hy.1, hy.2.le.trans hxb⟩)) (sub_nonpos.mpr hy.2.le)

theorem nonnegative_of_parabolic_inequality
    {u ut ux uxx κ β ℓ : ℝ → ℝ → ℝ} {t₀ t₁ a b : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ Icc a b))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hk : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 ≤ κ t x)
    (hl : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b, 0 < ℓ t x)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x ∈ Ioo a b,
      0 ≤ ut t x - κ t x * uxx t x - β t x * ux t x + ℓ t x * u t x)
    (hinit : ∀ x ∈ Icc a b, 0 ≤ u t₀ x)
    (hleft : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t a)
    (hright : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t b) :
    ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Icc a b, 0 ≤ u t x := by
  intro t htmem x hxmem
  by_contra hn
  have hnegative : u t x < 0 := lt_of_not_ge hn
  obtain ⟨p, hp, hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(t,x), htmem, hxmem⟩ hc
  have hpneg : u p.1 p.2 < 0 := lt_of_le_of_lt (hm (show (t, x) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨htmem, hxmem⟩)) hnegative
  have hpt : p.1 ∈ Ioc t₀ t₁ := by
    refine ⟨lt_of_le_of_ne hp.1.1 ?_, hp.1.2⟩
    intro heq
    have hz := hinit p.2 hp.2
    rw [heq] at hz
    exact (not_lt_of_ge hz) hpneg
  have hpx : p.2 ∈ Ioo a b := by
    constructor
    · refine lt_of_le_of_ne hp.2.1 ?_
      intro heq
      have hz := hleft p.1 hp.1
      rw [heq] at hz
      exact (not_lt_of_ge hz) hpneg
    · refine lt_of_le_of_ne hp.2.2 ?_
      intro heq
      have hz := hright p.1 hp.1
      rw [← heq] at hz
      exact (not_lt_of_ge hz) hpneg
  have hmintime : IsMinOn (fun s => u s p.2) (Icc t₀ t₁) p.1 := by
    intro s hs
    exact hm (show (s, p.2) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨hs, hp.2⟩)
  have hut : ut p.1 p.2 ≤ 0 :=
    time_derivative_nonpositive hpt.1 hpt.2 (ht p.1 hpt p.2 hpx) hmintime
  have hminspace : IsMinOn (u p.1) (Icc a b) p.2 := by
    intro y hy
    exact hm (show (p.1, y) ∈ Icc t₀ t₁ ×ˢ Icc a b from ⟨hp.1, hy⟩)
  have hlocal := hminspace.isLocalMin (Icc_mem_nhds hpx.1 hpx.2)
  have hux : ux p.1 p.2 = 0 := hlocal.hasDerivAt_eq_zero (hx p.1 hpt p.2 hpx)
  have huxx : 0 ≤ uxx p.1 p.2 :=
    second_derivative_nonnegative_at_min (hs p.1 hp.1) hlocal (hxx p.1 hpt p.2 hpx)
  have h1 := mul_nonneg (hk p.1 hpt p.2 hpx) huxx
  have h2 := mul_neg_of_pos_of_neg (hl p.1 hpt p.2 hpx) hpneg
  have h3 := hpde p.1 hpt p.2 hpx
  rw [hux, mul_zero, sub_zero] at h3
  linarith

end ZeroTemperatureSK.Parabolic

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.FullLineComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Parabolic

theorem nonnegative_fullLine_bounded
    {u ut ux uxx β c : ℝ → ℝ → ℝ} {t₀ t₁ C K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ univ))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hb : ∀ t ∈ Ioc t₀ t₁, ∀ x, β t x*x ≤ K*(1+x^2))
    (hbound : ∀ t ∈ Ioc t₀ t₁, ∀ x, c t x ≤ C)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      0 ≤ ut t x-(1/2:ℝ)*uxx t x-β t x*ux t x-c t x*u t x)
    (hlower : ∀ t ∈ Icc t₀ t₁, ∀ x, -M ≤ u t x)
    (hinit : ∀ x, 0 ≤ u t₀ x) :
    ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ u t x := by
  let k := max C 0+2*K+2
  let E (t : ℝ) := Real.exp (-k*(t-t₀))
  have hk : 0 < k := by dsimp [k]; linarith [le_max_right C 0]
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEd (t : ℝ) : HasDerivAt E (-k*E t) t := by
    convert ((((hasDerivAt_id t).sub_const t₀).const_mul (-k)).exp) using 1 <;> dsimp [E,id]
    ring
  have hEle (t : ℝ) (ht : t ∈ Icc t₀ t₁) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sub_nonneg.mpr ht.1))
  have hperturb (ε : ℝ) (hε : 0 < ε) (t : ℝ) (htm : t ∈ Icc t₀ t₁)
      (x : ℝ) : 0 ≤ E t*u t x+ε*(1+x^2) := by
    let A := |x|+M/ε+1
    have hdiv : 0 ≤ M/ε := div_nonneg hM hε.le
    have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg x]
    have hxA : x ≤ A := by dsimp [A]; linarith [le_abs_self x]
    have hAx : -A ≤ x := by dsimp [A]; linarith [neg_abs_le x]
    have hAm : M ≤ ε*A := by
      have he : ε*(M/ε)=M := by field_simp
      dsimp [A]
      nlinarith [abs_nonneg x]
    have hAb : M ≤ ε*(1+A^2) := by
      nlinarith [mul_nonneg hε.le (sq_nonneg (A-1))]
    let V (t x : ℝ) := E t*u t x+ε*(1+x^2)
    have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc t₀ t₁ ×ˢ Icc (-A) A) := by
      apply ContinuousOn.add
      · exact (show Continuous (fun p : ℝ × ℝ => E p.1) by dsimp [E]; fun_prop).continuousOn.mul
          (hc.mono (prod_mono subset_rfl (subset_univ _)))
      · fun_prop
    have hVs (r : ℝ) (hr : r ∈ Icc t₀ t₁) : Continuous (V r) :=
      ((hs r hr).const_mul (E r)).add (by fun_prop)
    have hVt (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivWithinAt (fun s => V s y) (E r*(ut r y-k*u r y)) (Icc t₀ t₁) r := by
      convert (((hEd r).hasDerivWithinAt.mul (ht r hr y)).add_const (ε*(1+y^2))) using 1 <;> try rfl
      ring
    have hVx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivAt (V r) (E r*ux r y+ε*(2*y)) y := by
      convert ((hx r hr y).const_mul (E r)).add
        ((((hasDerivAt_id y).pow 2).const_add 1).const_mul ε) using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
    have hVxx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivAt (deriv (V r)) (E r*uxx r y+2*ε) y := by
      have heloc : deriv (V r) =ᶠ[𝓝 y] (fun z => E r*deriv (u r) z+ε*(2*z)) := by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
        have hp : HasDerivAt (fun z : ℝ => ε*(1+z^2)) (ε*(2*z)) z := by
          convert (((hasDerivAt_id z).pow 2).const_add 1).const_mul ε using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
        rw [(hx r hr z).deriv]
        exact (((hx r hr z).const_mul (E r)).add hp).deriv
      apply HasDerivAt.congr_of_eventuallyEq _ heloc
      convert ((hxx r hr y).const_mul (E r)).add
        (((hasDerivAt_id y).const_mul 2).const_mul ε) using 1 <;> first | rfl | ring
    have hl (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) : 0 < k-c r y := by
      have hh := hbound r hr y
      dsimp [k]
      linarith [le_max_left C 0]
    have hVp (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        0 ≤ E r*(ut r y-k*u r y)-(1/2:ℝ)*(E r*uxx r y+2*ε)-
          β r y*(E r*ux r y+ε*(2*y))+(k-c r y)*V r y := by
      have hp := mul_nonneg (hEp r).le (hpde r hr y)
      have hc' : 2*K+2 ≤ k-c r y := by
        have hh := hbound r hr y
        dsimp [k]
        linarith [le_max_left C 0]
      have hprod := mul_le_mul_of_nonneg_right hc' (show 0 ≤ 1+y^2 by positivity)
      have hβ := hb r hr y
      have hbar : 0 ≤ (k-c r y)*(1+y^2)-1-2*β r y*y := by nlinarith [sq_nonneg y]
      have hh := mul_nonneg hε.le hbar
      dsimp [V]
      nlinarith
    have hVi (y : ℝ) (hy : y ∈ Icc (-A) A) : 0 ≤ V t₀ y := by
      exact add_nonneg (mul_nonneg (hEp t₀).le (hinit y)) (by positivity)
    have hVl (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r (-A) := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr (-A)) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    have hVr (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r A := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr A) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    exact nonnegative_of_parabolic_inequality hVc hVs hVt hVx hVxx (fun _ _ _ _ => by norm_num)
      hl hVp hVi hVl hVr t htm x ⟨hAx,hxA⟩
  intro t htt x
  have he : 0 ≤ E t*u t x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hq : 0 < 1+x^2 := by positivity
    have hh := hperturb (δ/(1+x^2)) (div_pos hδ hq) t htt x
    simpa only [div_mul_cancel₀ _ (ne_of_gt hq)] using hh
  exact (mul_nonneg_iff_of_pos_left (hEp t)).mp he

end ZeroTemperatureSK.Parabolic

end
end
section
open Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Parabolic

theorem nonnegative_halfLine_bounded
    {u ut ux uxx β c : ℝ → ℝ → ℝ} {t₀ t₁ C K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ Ici 0))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hb : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → β t x*x ≤ K*(1+x^2))
    (hbound : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      0 ≤ ut t x-(1/2:ℝ)*uxx t x-β t x*ux t x-c t x*u t x)
    (hlower : ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ x → -M ≤ u t x)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ u t₀ x)
    (hzero : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t 0) :
    ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ x → 0 ≤ u t x := by
  let k := max C 0+2*K+2
  let E (t : ℝ) := Real.exp (-k*(t-t₀))
  have hk : 0 < k := by dsimp [k]; linarith [le_max_right C 0]
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEd (t : ℝ) : HasDerivAt E (-k*E t) t := by
    convert ((((hasDerivAt_id t).sub_const t₀).const_mul (-k)).exp) using 1 <;> dsimp [E,id]
    ring
  have hEle (t : ℝ) (ht : t ∈ Icc t₀ t₁) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sub_nonneg.mpr ht.1))
  have hperturb (ε : ℝ) (hε : 0 < ε) (t : ℝ) (htm : t ∈ Icc t₀ t₁)
      (x : ℝ) (hxm : 0 ≤ x) : 0 ≤ E t*u t x+ε*(1+x^2) := by
    let A := x+M/ε+1
    have hdiv : 0 ≤ M/ε := div_nonneg hM hε.le
    have hA : 1 ≤ A := by dsimp [A]; linarith
    have hxA : x ≤ A := by dsimp [A]; linarith
    have hAm : M ≤ ε*A := by
      have he : ε*(M/ε)=M := by field_simp
      dsimp [A]
      nlinarith
    have hAb : M ≤ ε*(1+A^2) := by
      nlinarith [mul_nonneg hε.le (sq_nonneg (A-1))]
    let V (t x : ℝ) := E t*u t x+ε*(1+x^2)
    have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc t₀ t₁ ×ˢ Icc 0 A) := by
      apply ContinuousOn.add
      · exact (show Continuous (fun p : ℝ × ℝ => E p.1) by dsimp [E]; fun_prop).continuousOn.mul
          (hc.mono (by intro p hp; exact ⟨hp.1,hp.2.1⟩))
      · fun_prop
    have hVs (r : ℝ) (hr : r ∈ Icc t₀ t₁) : Continuous (V r) :=
      ((hs r hr).const_mul (E r)).add (by fun_prop)
    have hVt (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivWithinAt (fun s => V s y) (E r*(ut r y-k*u r y)) (Icc t₀ t₁) r := by
      convert (((hEd r).hasDerivWithinAt.mul (ht r hr y hy.1)).add_const (ε*(1+y^2))) using 1 <;> try rfl
      ring
    have hVx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivAt (V r) (E r*ux r y+ε*(2*y)) y := by
      convert ((hx r hr y hy.1).const_mul (E r)).add
        ((((hasDerivAt_id y).pow 2).const_add 1).const_mul ε) using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
    have hVxx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivAt (deriv (V r)) (E r*uxx r y+2*ε) y := by
      have heloc : deriv (V r) =ᶠ[𝓝 y] (fun z => E r*deriv (u r) z+ε*(2*z)) := by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
        have hp : HasDerivAt (fun z : ℝ => ε*(1+z^2)) (ε*(2*z)) z := by
          convert (((hasDerivAt_id z).pow 2).const_add 1).const_mul ε using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
        rw [(hx r hr z hz.1).deriv]
        exact (((hx r hr z hz.1).const_mul (E r)).add hp).deriv
      apply HasDerivAt.congr_of_eventuallyEq _ heloc
      convert ((hxx r hr y hy.1).const_mul (E r)).add
        (((hasDerivAt_id y).const_mul 2).const_mul ε) using 1 <;> first | rfl | ring
    have hl (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) : 0 < k-c r y := by
      have hh := hbound r hr y hy.1
      dsimp [k]
      linarith [le_max_left C 0]
    have hVp (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        0 ≤ E r*(ut r y-k*u r y)-(1/2:ℝ)*(E r*uxx r y+2*ε)-
          β r y*(E r*ux r y+ε*(2*y))+(k-c r y)*V r y := by
      have hp := mul_nonneg (hEp r).le (hpde r hr y hy.1)
      have hc' : 2*K+2 ≤ k-c r y := by
        have hh := hbound r hr y hy.1
        dsimp [k]
        linarith [le_max_left C 0]
      have hprod := mul_le_mul_of_nonneg_right hc' (show 0 ≤ 1+y^2 by positivity)
      have hβ := hb r hr y hy.1
      have hbar : 0 ≤ (k-c r y)*(1+y^2)-1-2*β r y*y := by nlinarith [sq_nonneg y]
      have hh := mul_nonneg hε.le hbar
      dsimp [V]
      nlinarith
    have hVi (y : ℝ) (hy : y ∈ Icc 0 A) : 0 ≤ V t₀ y := by
      exact add_nonneg (mul_nonneg (hEp t₀).le (hinit y hy.1)) (by positivity)
    have hVl (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r 0 := by
      exact add_nonneg (mul_nonneg (hEp r).le (hzero r hr)) (by positivity)
    have hVr (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r A := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr A (by linarith)) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    exact nonnegative_of_parabolic_inequality hVc hVs hVt hVx hVxx (fun _ _ _ _ => by norm_num)
      hl hVp hVi hVl hVr t htm x ⟨hxm,hxA⟩
  intro t htt x hxx
  have he : 0 ≤ E t*u t x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hq : 0 < 1+x^2 := by positivity
    have hh := hperturb (δ/(1+x^2)) (div_pos hδ hq) t htt x hxx
    simpa only [div_mul_cancel₀ _ (ne_of_gt hq)] using hh
  exact (mul_nonneg_iff_of_pos_left (hEp t)).mp he

end ZeroTemperatureSK.Parabolic

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.BackwardComparison
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

lemma bounded_linear_nonpositive {F r Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hr : BoundedSmoothFamily r)
    (hcont : ∀ T, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x, 0 < x →
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+r t x*deriv (F t) x+c t x*F t x)
    (hzero : ∀ t, 0 ≤ t → F t 0=0)
    (hinit : ∀ x, 0 ≤ x → F 0 x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → F t x ≤ 0 := by
  obtain ⟨R,hR⟩ := hr.bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x hx
  have hh := Parabolic.nonnegative_halfLine_bounded
    (u := fun t x => - F t x) (ut := fun t x => -Ft t x)
    (ux := fun t x => -deriv (F t) x) (uxx := fun t x => -iteratedDeriv 2 (F t) x)
    (β := r) (c := c) (C := C) (K := (R:ℝ)) (M := (M:ℝ)) R.coe_nonneg M.coe_nonneg
    ((hcont T).neg.mono (prod_mono subset_rfl (subset_univ _)))
    (fun t _ => (hF.regular t).smooth.continuous.neg)
    (fun t ht x _ => (htime t ht.1 x).neg.hasDerivWithinAt)
    (fun t _ x _ => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt.neg)
    (fun t _ x _ => ?_) (fun t _ x hxp => ?_)
    (fun t ht x hxp => hc t ht.1 x hxp)
    (fun t ht x hxp => ?_)
    (fun t _ x _ => neg_le_neg ((le_abs_self _).trans (hM t x)))
    (fun x hx => neg_nonneg.mpr (hinit x hx))
    (fun t ht => by rw [hzero t ht.1]; simp) T ⟨hT,le_rfl⟩ x hx
  · exact neg_nonneg.mp hh
  · have he : deriv (fun y => -F t y) = fun y => -deriv (F t) y :=
      funext (fun y => ((hF.regular t).smooth.differentiable (by simp) y).hasDerivAt.neg.deriv)
    rw [he]
    convert (hasDerivAt_spatialJet (hF.regular t).smooth 1 x).neg using 1 <;> try rfl
    first | rfl | (simp only [iteratedDeriv_one]; rfl)
  · have hb := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hR t x)) hxp.le
    have hh : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1)]
    exact hb.trans (mul_le_mul_of_nonneg_left hh R.coe_nonneg)
  · rw [hpde t ht.1 x hxp]
    ring_nf
    exact le_rfl

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma second_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) :
    Function.Odd (iteratedDeriv 2 (r t)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
   (even_deriv_odd ((hr.family.deriv.regular t).smooth.differentiable (by simp))
    (odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)))

theorem second_nonpos (ho : ∀ t, Function.Odd (r t))
    (hi : ∀ x, 0 ≤ x → iteratedDeriv 2 (r 0) x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (r t) x ≤ 0 := by
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  apply bounded_linear_nonpositive (hr.family.iteratedDeriv 2) hr.family
    (fun T => hr.jet_continuous 2 T) (fun t ht x => hr.time_derivative 2 t ht x)
    (c := fun t x => 3*deriv (r t) x) (C := 3*(V:ℝ))
  · intro t ht x hx
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hV t x)) (by norm_num)
  · intro t ht x hx
    rw [hr.rate_jet2]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  · intro t ht
    have hh := hr.second_odd ho t 0
    simp only [neg_zero] at hh
    linarith
  · exact hi

theorem rate_nonpos (ho : ∀ t, Function.Odd (r t))
    (hi : ∀ x, 0 ≤ x → burgersRate r 0 x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → burgersRate r t x ≤ 0 := by
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  apply bounded_linear_nonpositive hr.rate_family hr.family hr.rate_continuous
    (fun t ht x => hr.rate_time ht x) (c := fun t x => deriv (r t) x) (C := (V:ℝ))
  · intro t ht x hx
    exact (le_abs_self _).trans (hV t x)
  · intro t ht x hx
    rfl
  · intro t ht
    have hh := hr.rate_odd ho t 0
    simp only [neg_zero] at hh
    linarith
  · exact hi

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat
namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma pos_halfLine (ho : ∀ t, Function.Odd (r t))
    (hv : ∀ t, 0 ≤ t → ∀ x, 0 < deriv (r t) x) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    0 < r t x := by
  have hm : StrictMono (r t) := strictMonoOn_univ.1 <|
    strictMonoOn_of_deriv_pos convex_univ (hr.family.regular t).smooth.continuous.continuousOn
      (fun spatial _ => hv t ht spatial)
  have hz : r t 0=0 := by
    have hh := ho t 0
    simp only [neg_zero] at hh
    linarith
  simpa only [hz] using hm hx

theorem wronskian_nonneg (ho : ∀ t, Function.Odd (r t))
    (hv : ∀ t, 0 ≤ t → ∀ x, 0 < deriv (r t) x)
    (hiw : ∀ x, 0 ≤ x → iteratedDeriv 2 (r 0) x ≤ 0)
    (hip : ∀ x, 0 ≤ x → burgersRate r 0 x ≤ 0)
    (hiK : ∀ x, 0 ≤ x → 0 ≤ backwardWronskian r 0 x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → 0 ≤ backwardWronskian r t x := by
  have hw := hr.second_nonpos ho hiw
  have hp := hr.rate_nonpos ho hip
  obtain ⟨R,hR⟩ := hr.family.bound
  obtain ⟨M,hM⟩ := hr.wronskian_family.bound
  intro T hT x hx
  apply Parabolic.nonnegative_halfLine_bounded
    (u := backwardWronskian r) (ut := wronskianRate r)
    (ux := fun t => deriv (backwardWronskian r t))
    (uxx := fun t => iteratedDeriv 2 (backwardWronskian r t))
    (β := fun t x => r t x-deriv (r t) x/r t x)
    (c := fun t x => 2*(burgersRate r t x/r t x)) (C := 0) (K := (R:ℝ)) (M := (M:ℝ))
    R.coe_nonneg M.coe_nonneg
    ((hr.wronskian_continuous T).mono (prod_mono subset_rfl (subset_univ _)))
    (fun t _ => (hr.wronskian_family.regular t).smooth.continuous)
    (fun t ht x _ => (hr.wronskian_time ht.1 x).hasDerivWithinAt)
    (fun t _ x _ => ((hr.wronskian_family.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x _ => by simpa only [iteratedDeriv_one] using
      hasDerivAt_spatialJet (hr.wronskian_family.regular t).smooth 1 x)
    (fun t ht x hx => ?_) (fun t ht x hx => ?_) (fun t ht x hx => ?_)
    (fun t _ x _ => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hiK
    (fun t ht => ?_) T ⟨hT,le_rfl⟩ x hx
  · have hpos := hr.pos_halfLine ho hv ht.1.le hx
    have hsub : 0 ≤ deriv (r t) x/r t x*x :=
      mul_nonneg (div_nonneg (hv t ht.1.le x).le hpos.le) hx.le
    have hb := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hR t x)) hx.le
    have hxx : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1)]
    have hlast := mul_le_mul_of_nonneg_left hxx R.coe_nonneg
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (div_nonpos_of_nonpos_of_nonneg (hp t ht.1.le x hx.le) (hr.pos_halfLine ho hv ht.1.le hx).le)
  · rw [hr.wronskian_equation t x (ne_of_gt (hr.pos_halfLine ho hv ht.1.le hx))]
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (hr.pos_halfLine ho hv ht.1.le hx).le (hw t ht.1.le x hx.le))
      (hp t ht.1.le x hx.le)
  · have hh := hr.wronskian_odd ho t 0
    simp only [neg_zero] at hh
    linarith

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.BackwardRescale
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

lemma scaled_jet {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => α*r y) x = α*iteratedDeriv n r x :=
  iteratedDeriv_const_mul α (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)

lemma scaled_rate {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α x : ℝ) :
    burgersRate (fun _ y => α*r y) 0 x =
      α*burgersRate (fun _ => r) 0 x+α*(α-1)*r x*deriv r x := by
  have he := scaled_jet hr α 1 x
  simp only [iteratedDeriv_one] at he
  simp only [burgersRate,scaled_jet hr α 2 x,he]
  ring

lemma scaled_wronskian {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (α x : ℝ) :
    backwardWronskian (fun _ y => α*r y) 0 x =
      α^2*backwardWronskian (fun _ => r) 0 x+
        α^2*(α-1)*(r x)^2*iteratedDeriv 2 r x := by
  have hr' := contDiff_iteratedDeriv_infty hr 1
  have hr'' := contDiff_iteratedDeriv_infty hr 2
  have hp : ContDiff ℝ ∞ (burgersRate (fun _ => r) 0) := by
    exact (contDiff_const.mul hr'').add (hr.mul (by simpa only [iteratedDeriv_one] using hr'))
  have he : burgersRate (fun _ y => α*r y) 0 = fun y =>
      α*burgersRate (fun _ => r) 0 y+α*(α-1)*r y*deriv r y := funext (scaled_rate hr α)
  have hd := ((hp.differentiable (by simp) x).hasDerivAt.const_mul α).add
    (((hasDerivAt_spatialJet hr 0 x).const_mul (α*(α-1))).mul (hasDerivAt_spatialJet hr 1 x))
  have hd' : HasDerivAt (burgersRate (fun _ y => α*r y) 0)
      (α*deriv (burgersRate (fun _ => r) 0) x+
        α*(α-1)*((deriv r x)^2+r x*iteratedDeriv 2 r x)) x := by
    rw [he]
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  have he' := scaled_jet hr α 1 x
  simp only [iteratedDeriv_one] at he'
  rw [backwardWronskian,hd'.deriv,he',scaled_rate hr α x]
  simp only [backwardWronskian]
  ring

theorem BackwardShape.rescale {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : BackwardShape r)
    {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) : BackwardShape (fun x => α*r x) := by
  have hv : ∀ x, deriv (fun y => α*r y) x=α*deriv r x := fun x => by
    simpa only [iteratedDeriv_one] using scaled_jet hr α 1 x
  have hzero : r 0=0 := by
    have hh := hs.odd 0
    simp only [neg_zero] at hh
    linarith
  have hpos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x := by
    have hm := (strictMono_of_deriv_pos hs.derivative_pos).monotone hx
    simpa only [hzero] using hm
  refine ⟨?_,fun x => by rw [hv]; exact mul_pos hα (hs.derivative_pos x),?_,?_,?_⟩
  · intro x
    change α*r (-x) = -(α*r x)
    rw [hs.odd x]
    ring
  · intro x hx
    rw [scaled_jet hr α]
    exact mul_nonpos_of_nonneg_of_nonpos hα.le (hs.second_nonpos x hx)
  · intro x hx
    rw [scaled_rate hr α]
    apply add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα.le (hs.rate_nonpos x hx))
    apply mul_nonpos_of_nonpos_of_nonneg _ (hs.derivative_pos x).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hα.le (sub_nonpos.mpr hα')) (hpos x hx)
  · intro x hx
    rw [scaled_wronskian hr α]
    apply add_nonneg (mul_nonneg (sq_nonneg α) (hs.wronskian_nonneg x hx))
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) (sub_nonpos.mpr hα')) (sq_nonneg (r x)))
      (hs.second_nonpos x hx)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.TerminalShapes
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

lemma tanh_scaled_derivative (M x : ℝ) :
    HasDerivAt (fun y => Real.tanh (M*y)) (M*(1-(Real.tanh (M*x))^2)) x := by
  convert (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M) using 1 <;>
    first | rfl | ring

lemma tanhDrift_derivative (c M x : ℝ) :
    HasDerivAt (tanhDrift c M) (c*M*(1-(Real.tanh (M*x))^2)) x := by
  convert (tanh_scaled_derivative M x).const_mul c using 1 <;> first | rfl | ring

lemma tanhDrift_second (c M x : ℝ) :
    iteratedDeriv 2 (tanhDrift c M) x = -2*c*M^2*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
  have he : deriv (tanhDrift c M) = fun y => c*M*(1-(Real.tanh (M*y))^2) :=
    funext (fun y => (tanhDrift_derivative c M y).deriv)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert ((((tanh_scaled_derivative M x).pow 2).const_sub 1).const_mul (c*M)).deriv using 1 <;> try rfl
  ring

lemma tanhDrift_rate (c M x : ℝ) :
    burgersRate (fun _ => tanhDrift c M) 0 x =
      c*M*(c-M)*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
  rw [burgersRate,tanhDrift_second,(tanhDrift_derivative c M x).deriv]
  dsimp only [tanhDrift]
  ring

lemma tanhDrift_wronskian (c M x : ℝ) :
    backwardWronskian (fun _ => tanhDrift c M) 0 x =
      2*c^2*M^2*(M-c)*(Real.tanh (M*x))^3*(1-(Real.tanh (M*x))^2) := by
  have he : burgersRate (fun _ => tanhDrift c M) 0 = fun y =>
      c*M*(c-M)*Real.tanh (M*y)*(1-(Real.tanh (M*y))^2) := funext (tanhDrift_rate c M)
  have hd := ((tanh_scaled_derivative M x).const_mul (c*M*(c-M))).mul
    (((tanh_scaled_derivative M x).pow 2).const_sub 1)
  have hd' : HasDerivAt (fun y => c*M*(c-M)*Real.tanh (M*y)*(1-(Real.tanh (M*y))^2))
      (c*M^2*(c-M)*(1-(Real.tanh (M*x))^2)*(1-3*(Real.tanh (M*x))^2)) x := by
    convert hd using 1 <;> try rfl
    simp only [Pi.pow_apply]
    ring
  rw [backwardWronskian,he,hd'.deriv,(tanhDrift_derivative c M x).deriv]
  dsimp only [tanhDrift]
  ring

lemma tanh_sq_gap_pos (y : ℝ) : 0 < 1-(Real.tanh y)^2 := by
  have hh := Real.abs_tanh_lt_one y
  nlinarith [sq_abs (Real.tanh y),abs_nonneg (Real.tanh y)]

lemma tanh_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le

lemma tanhDrift_initial_signs {c M : ℝ} (hc : 0 < c) (hM : c ≤ M) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 2 (tanhDrift c M) x ≤ 0 ∧
    burgersRate (fun _ => tanhDrift c M) 0 x ≤ 0 ∧
    0 ≤ backwardWronskian (fun _ => tanhDrift c M) 0 x := by
  have hMp : 0 < M := hc.trans_le hM
  have hT := tanh_nonneg_of_nonneg (mul_nonneg hMp.le hx)
  have hD := (tanh_sq_gap_pos (M*x)).le
  rw [tanhDrift_second,tanhDrift_rate,tanhDrift_wronskian]
  refine ⟨?_,?_,?_⟩
  · apply mul_nonpos_of_nonpos_of_nonneg _ hD
    apply mul_nonpos_of_nonpos_of_nonneg _ hT
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg M)
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hc.le
  · apply mul_nonpos_of_nonpos_of_nonneg _ hD
    apply mul_nonpos_of_nonpos_of_nonneg _ hT
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hMp.le) (sub_nonpos.mpr hM)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hM))
      (pow_nonneg hT _)) hD

lemma gaussianBurgers_terminal {f : ℝ → ℝ} (c : ℝ) :
    gaussianBurgers c f 0 = fun x => c*deriv f x := by
  have he : varianceLogHeat c 0 f = f := funext (fun x => by
    simpa only [backward,sub_self] using backward_terminal c 0 f x)
  funext x
  rw [gaussianBurgers,he]

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.FiniteStrictConvex
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

lemma softAbs_curvature_pos {M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < deriv (deriv (softAbs M)) x := by
  have he : deriv (softAbs M) = fun y => Real.tanh (M*y) :=
    funext (fun y => (hasDerivAt_softAbs (ne_of_gt hM) y).deriv)
  rw [he]
  have hd := (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd' : HasDerivAt (fun y => Real.tanh (M*y)) ((1-(Real.tanh (M*x))^2)*M) x := by
    simpa only [Function.comp_def,id_eq,mul_one] using hd
  rw [hd'.deriv]
  have hh := Real.abs_tanh_lt_one (M*x)
  have hs : (Real.tanh (M*x))^2 < 1 := by nlinarith [sq_abs (Real.tanh (M*x)),abs_nonneg (Real.tanh (M*x))]
  exact mul_pos (sub_pos.mpr hs) hM

lemma cascade_curvature_pos {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hpos : ∀ x, 0 < deriv (deriv f) x) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (x : ℝ) :
    0 < deriv (deriv (cascade c h f N i)) x := by
  induction N generalizing i x with
  | zero => exact hpos x
  | succ N ih =>
    exact logSemigroup_curvature_pos (cascade_regular hf hLip c h N (i+1))
      (cascade_lipschitz hLip c h N (i+1)) (ih (i+1)) (c i).coe_nonneg h x

lemma varianceLogHeat_curvature_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hpos : ∀ x, 0 < deriv (deriv f) x)
    {c : ℝ} (hc : 0 ≤ c) (t x : ℝ) :
    0 < deriv (deriv (varianceLogHeat c t f)) x := by
  have he : varianceLogHeat c t f = logSemigroup c (Real.toNNReal t) f :=
    funext (varianceLogHeat_eq_logSemigroup_toNNReal hf.smooth.continuous.measurable c t)
  rw [he]
  exact logSemigroup_curvature_pos hf hLip hpos hc _ x

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.AffineComparison
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

lemma AffineSmoothFamily.drift_bound {β : ℝ → ℝ → ℝ} (hβ : AffineSmoothFamily β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x, β t x*x ≤ K*(1+x^2) := by
  obtain ⟨C,hC,hb⟩ := hβ.bound
  refine ⟨2*C,by positivity,fun t x => ?_⟩
  have hh : β t x*x ≤ C*(1+|x|)*|x| := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb t x) (abs_nonneg x)
  have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hmul := mul_le_mul_of_nonneg_left hx hC
  have he : |x| * |x| = x*x := by nlinarith [sq_abs x]
  nlinarith [mul_nonneg hC (sq_nonneg x)]

lemma affineDrift_nonnegative_full {F β Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hβ : AffineSmoothFamily β)
    (hcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x,
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+β t x*deriv (F t) x+c t x*F t x)
    (hinit : ∀ x, 0 ≤ F 0 x) : ∀ t, 0 ≤ t → ∀ x, 0 ≤ F t x := by
  obtain ⟨K,hK,hβb⟩ := hβ.drift_bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x
  apply Parabolic.nonnegative_fullLine_bounded (u := F) (ut := Ft)
    (ux := fun t => deriv (F t)) (uxx := fun t => iteratedDeriv 2 (F t))
    (β := β) (c := c) (C := C) (K := K) (M := (M:ℝ)) hK M.coe_nonneg
    hcont.continuousOn (fun t _ => (hF.regular t).smooth.continuous)
    (fun t ht x => (htime t ht.1 x).hasDerivWithinAt)
    (fun t _ x => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x => by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet (hF.regular t).smooth 1 x)
    (fun t _ x => hβb t x) (fun t ht x => hc t ht.1 x)
    (fun t ht x => by rw [hpde t ht.1 x];ring_nf;exact le_rfl)
    (fun t _ x => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hinit T ⟨hT,le_rfl⟩ x

lemma affineDrift_nonnegative_half {F β Ft c : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : BoundedSmoothFamily F) (hβ : AffineSmoothFamily β)
    (hcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (htime : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (Ft t x) t)
    (hc : ∀ t, 0 < t → ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t, 0 < t → ∀ x, 0 < x →
      Ft t x=(1/2:ℝ)*iteratedDeriv 2 (F t) x+β t x*deriv (F t) x+c t x*F t x)
    (hzero : ∀ t, 0 ≤ t → 0 ≤ F t 0)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ F 0 x) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → 0 ≤ F t x := by
  obtain ⟨K,hK,hβb⟩ := hβ.drift_bound
  obtain ⟨M,hM⟩ := hF.bound
  intro T hT x hx
  apply Parabolic.nonnegative_halfLine_bounded (u := F) (ut := Ft)
    (ux := fun t => deriv (F t)) (uxx := fun t => iteratedDeriv 2 (F t))
    (β := β) (c := c) (C := C) (K := K) (M := (M:ℝ)) hK M.coe_nonneg
    hcont.continuousOn (fun t _ => (hF.regular t).smooth.continuous)
    (fun t ht x _ => (htime t ht.1 x).hasDerivWithinAt)
    (fun t _ x _ => ((hF.regular t).smooth.differentiable (by simp) x).hasDerivAt)
    (fun t _ x _ => by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet (hF.regular t).smooth 1 x)
    (fun t _ x _ => hβb t x) (fun t ht x hx => hc t ht.1 x hx)
    (fun t ht x hx => by rw [hpde t ht.1 x hx];ring_nf;exact le_rfl)
    (fun t _ x _ => (neg_le_neg (hM t x)).trans (neg_abs_le _)) hinit
    (fun t ht => hzero t ht.1) T ⟨hT,le_rfl⟩ x hx

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ForwardSigns
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
namespace SmoothForward
variable {s : ℝ → ℝ → ℝ} (hs : SmoothForward s)
include hs

theorem deriv_ge_inverse {a : ℝ} (ha : 0 < a)
    (hi : ∀ x, a⁻¹ ≤ deriv (s 0) x) :
    ∀ t, 0 ≤ t → ∀ x, (forwardTime a t)⁻¹ ≤ deriv (s t) x := by
  let F (t x : ℝ) := deriv (s t) x-(forwardTime a t)⁻¹
  let Ft (t x : ℝ) := deriv (scoreRate s t) x+((forwardTime a t)⁻¹)^2
  have hF : BoundedSmoothFamily F := by
    convert hs.deriv_family.add ((inverse_forwardTime_family ha).const_mul (-1)) using 1 <;> try rfl
    funext t x
    simp only [F,neg_one_mul,sub_eq_add_neg]
  have hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
    hs.family.deriv.continuous.sub ((inverse_forwardTime_continuous ha).comp continuous_fst)
  have hFt (t : ℝ) (ht : 0 < t) (x : ℝ) : HasDerivAt (fun u => F u x) (Ft t x) t := by
    have hb := (hasDerivAt_forwardTime (a := a) ht).inv (ne_of_gt (forwardTime_pos ha t))
    convert (hs.time_derivative 1 t ht x).sub hb using 1 <;>
     first | rfl | ((try funext u); simp only [F,Ft,iteratedDeriv_one,Pi.sub_apply,Pi.inv_apply] <;> ring)
  have hFx (t x : ℝ) : deriv (F t) x=iteratedDeriv 2 (s t) x := by
    simpa only [F,iteratedDeriv_one] using ((hs.jet_spatial 1 t x).sub_const ((forwardTime a t)⁻¹)).deriv
  have hFxx (t x : ℝ) : iteratedDeriv 2 (F t) x=iteratedDeriv 3 (s t) x := by
    rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,show deriv (F t)=iteratedDeriv 2 (s t) from funext (hFx t)]
    exact (hs.jet_spatial 2 t x).deriv
  have hβ : AffineSmoothFamily (fun t x => -s t x) := by
    simpa only [neg_one_mul] using hs.family.const_mul (-1)
  obtain ⟨V,hV⟩ := hs.deriv_family.bound
  have hh := affineDrift_nonnegative_full hF hβ hFc hFt
    (c := fun t x => -(deriv (s t) x+(forwardTime a t)⁻¹)) (C := (V:ℝ))
    (fun t ht x => ?_) (fun t ht x => ?_) (fun x => ?_)
  · intro t ht x
    exact sub_nonneg.mp (hh t ht x)
  · have hb := inv_pos.mpr (forwardTime_pos ha t)
    have hv := (neg_abs_le (deriv (s t) x)).trans' (neg_le_neg (hV t x))
    linarith
  · rw [hFx,hFxx]
    dsimp only [Ft,F]
    rw [hs.rate_deriv]
    ring
  · simpa only [F,forwardTime,max_self,add_zero] using sub_nonneg.mpr (hi x)

theorem second_nonpos (ho : ∀ t, Function.Odd (s t))
    (hi : ∀ x, 0 ≤ x → iteratedDeriv 2 (s 0) x ≤ 0) :
    ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0 := by
  let F (t x : ℝ) := -iteratedDeriv 2 (s t) x
  have hF : BoundedSmoothFamily F := by
    simpa only [neg_one_mul] using (hs.jet_family 1).const_mul (-1)
  have hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := (hs.jet_continuous 2).neg
  have hFx (t x : ℝ) : deriv (F t) x= -iteratedDeriv 3 (s t) x :=
    ((hs.jet_spatial 2 t x).neg).deriv
  have hFxx (t x : ℝ) : iteratedDeriv 2 (F t) x= -iteratedDeriv 4 (s t) x := by
    rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,show deriv (F t)=(fun x => -iteratedDeriv 3 (s t) x) from funext (hFx t)]
    exact ((hs.jet_spatial 3 t x).neg).deriv
  have hβ : AffineSmoothFamily (fun t x => -s t x) := by
    simpa only [neg_one_mul] using hs.family.const_mul (-1)
  obtain ⟨V,hV⟩ := hs.deriv_family.bound
  have hh := affineDrift_nonnegative_half hF hβ hFc
    (fun t ht x => (hs.time_derivative 2 t ht x).neg)
    (c := fun t x => -3*deriv (s t) x) (C := 3*(V:ℝ))
    (fun t ht x hx => ?_) (fun t ht x hx => ?_) (fun t ht => ?_) (fun x hx => neg_nonneg.mpr (hi x hx))
  · intro t ht x hx
    exact neg_nonneg.mp (hh t ht x hx)
  · have hv := (neg_abs_le (deriv (s t) x)).trans' (neg_le_neg (hV t x))
    linarith
  · rw [hFx,hFxx,hs.rate_jet2]
    dsimp only [F]
    ring
  · have hz := hs.second_odd ho t 0
    simp only [neg_zero] at hz
    dsimp [F]
    linarith

end SmoothForward
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma forwardCorrection_shape {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hshape : ForwardDatumShape f)
    {t : ℝ} (ht : 0 ≤ t) : ForwardDatumShape (forwardCorrection a f t) := by
  have hi (x : ℝ) : a⁻¹ ≤ deriv (forwardScore a f 0) x := by
    rw [forwardScore_deriv hf hLip,forwardCorrection_terminal a (ne_of_gt ha),forwardTime]
    simp only [max_self,add_zero]
    linarith [hshape.second x]
  have hge := (forwardScore_smooth ha hf hLip).deriv_ge_inverse ha hi t ht
  have h₂ : ∀ x, iteratedDeriv 2 (forwardCorrection a f t) x ≤ 0 := by
    intro x
    have hh := hge x
    rw [forwardScore_deriv hf hLip] at hh
    linarith
  have hi₂ (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 2 (forwardScore a f 0) x ≤ 0 := by
    rw [forwardScore_second hf hLip,forwardCorrection_terminal a (ne_of_gt ha)]
    exact neg_nonpos.mpr (hshape.third x hx)
  have hle := (forwardScore_smooth ha hf hLip).second_nonpos (forwardScore_odd hf hLip hshape.even) hi₂ t ht
  refine ⟨forwardCorrection_even hf hLip hshape.even t,h₂,fun x hx => ?_⟩
  have hh := hle x hx
  rw [forwardScore_second hf hLip] at hh
  exact neg_nonpos.mp hh

lemma ForwardDatumShape.const (c : ℝ) : ForwardDatumShape (fun _ : ℝ => c) := by
  refine ⟨fun _ => rfl,fun x => ?_,fun x hx => ?_⟩ <;> simp [iteratedDeriv_const]

lemma ForwardDatumShape.jump {f φ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hshape : ForwardDatumShape f) (heφ : Function.Even φ)
    (hv : ∀ x, 0 ≤ iteratedDeriv 2 φ x) (hw : ∀ x, 0 ≤ x → iteratedDeriv 3 φ x ≤ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) : ForwardDatumShape (fun x => f x-δ*φ x) := by
  have hj (n : ℕ) (x : ℝ) : iteratedDeriv n (fun x => f x-δ*φ x) x =
      iteratedDeriv n f x-δ*iteratedDeriv n φ x := by
    rw [iteratedDeriv_fun_sub (n := n)
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
      ((contDiff_const.mul hφ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt),
      iteratedDeriv_const_mul_field]
  refine ⟨?_,?_,?_⟩
  · intro x
    change f (-x) - δ * φ (-x) = f x - δ * φ x
    rw [hshape.even x,heφ x]
  · intro x
    rw [hj]
    linarith [hshape.second x,mul_nonneg hδ (hv x)]
  · intro x hx
    rw [hj]
    linarith [hshape.third x hx,mul_nonpos_of_nonneg_of_nonpos hδ (hw x hx)]

end ZeroTemperatureSK.Heat

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
-- module Solutions.OAIQW_ZeroTemperatureSK.Backward.GaussianBackwardShapes
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

theorem gaussianBurgers_shape {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    (hcurv : ∀ x, 0 < deriv (deriv f) x) {c : ℝ} (hc : 0 < c)
    (hi : BackwardShape (fun x => c*deriv f x))
    {t : ℝ} (ht : 0 ≤ t) : BackwardShape (gaussianBurgers c f t) := by
  have hr := gaussianBurgers_smooth hf hLip hc.le
  have ho := gaussianBurgers_odd hf hLip he hc.le
  have hz := gaussianBurgers_terminal (f := f) c
  have hiv : BackwardShape (gaussianBurgers c f 0) := by rw [hz]; exact hi
  have hv (s : ℝ) (_hs : 0 ≤ s) (x : ℝ) : 0 < deriv (gaussianBurgers c f s) x := by
    have hj := gaussianBurgers_jet hf hLip hc.le 1 s x
    simp only [iteratedDeriv_one] at hj
    rw [hj]
    exact mul_pos hc (by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      varianceLogHeat_curvature_pos hf hLip hcurv hc.le s x)
  refine ⟨ho t,hv t ht,?_,?_,?_⟩
  · exact hr.second_nonpos ho hiv.second_nonpos t ht
  · exact hr.rate_nonpos ho hiv.rate_nonpos t ht
  · exact hr.wronskian_nonneg ho hv hiv.second_nonpos hiv.rate_nonpos hiv.wronskian_nonneg t ht

theorem logSemigroup_backward_shape {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (he : Function.Even f)
    (hcurv : ∀ x, 0 < deriv (deriv f) x) {c : ℝ} (hc : 0 < c)
    (hi : BackwardShape (fun x => c*deriv f x)) (h : ℝ≥0) :
    BackwardShape (fun x => c*deriv (logSemigroup c h f) x) := by
  have hh := gaussianBurgers_shape hf hLip he hcurv hc hi h.coe_nonneg
  have heq : varianceLogHeat c h f = logSemigroup c h f :=
    funext (varianceLogHeat_eq_logSemigroup hf.smooth.continuous.measurable c h)
  have heq' : gaussianBurgers c f h = fun x => c*deriv (logSemigroup c h f) x := by
    funext x
    rw [gaussianBurgers,heq]
  rwa [heq'] at hh

lemma softAbs_backward_shape {M c : ℝ} (hc : 0 < c) (hM : c ≤ M) :
    BackwardShape (fun x => c*deriv (softAbs M) x) := by
  have hMp := hc.trans_le hM
  have he : (fun x => c*deriv (softAbs M) x) = tanhDrift c M := by
    funext x
    rw [(hasDerivAt_softAbs (ne_of_gt hMp) x).deriv]
    rfl
  rw [he]
  refine ⟨?_,?_,fun x hx => (tanhDrift_initial_signs hc hM x hx).1,
    fun x hx => (tanhDrift_initial_signs hc hM x hx).2.1,
    fun x hx => (tanhDrift_initial_signs hc hM x hx).2.2⟩
  · intro x
    simp only [tanhDrift,mul_neg,Real.tanh_neg]
  · intro x
    rw [(tanhDrift_derivative c M x).deriv]
    exact mul_pos (mul_pos hc hMp) (tanh_sq_gap_pos (M*x))

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

theorem cascade_backward_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) :
    BackwardShape (fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N i) x) := by
  have hMp : 0 < M := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hMp)
  have hLip := softAbs_lipschitz (ne_of_gt hMp)
  induction N generalizing i with
  | zero => exact softAbs_backward_shape (hc i) (hM i)
  | succ N ih =>
    have hdatum := cascade_regular hf hLip c h N (i+1)
    have hsmooth : ContDiff ℝ ∞ (fun x => (c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x) :=
      contDiff_const.mul hdatum.deriv_bounded.smooth
    have hir := BackwardShape.rescale hsmooth (ih (i+1))
      (div_pos (hc i) (hc (i+1)))
      ((div_le_one (hc (i+1))).mpr (show (c i:ℝ) ≤ c (i+1) from hmono (Nat.le_succ i)))
    have he : (fun x => ((c i:ℝ)/(c (i+1):ℝ))*
        ((c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x)) =
        fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x := by
      funext x
      field_simp [ne_of_gt (hc (i+1))]
    rw [he] at hir
    exact logSemigroup_backward_shape hdatum (cascade_lipschitz hLip c h N (i+1))
      (cascade_even hf hLip (softAbs_even M) c h N (i+1))
      (cascade_curvature_pos hf hLip (softAbs_curvature_pos hMp) c h N (i+1))
      (hc i) hir h

theorem finiteHead_backward_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) (t : ℝ) (ht : t ≤ h) :
    BackwardShape (fun x => (c i:ℝ)*deriv (finiteValue c h (softAbs M) (N+1) i t) x) := by
  have hMp : 0 < M := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hMp)
  have hLip := softAbs_lipschitz (ne_of_gt hMp)
  have hdatum := cascade_regular hf hLip c h N (i+1)
  have hsmooth : ContDiff ℝ ∞ (fun x => (c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x) :=
    contDiff_const.mul hdatum.deriv_bounded.smooth
  have hir := BackwardShape.rescale hsmooth (cascade_backward_shape c hc hmono hM h N (i+1))
    (div_pos (hc i) (hc (i+1)))
    ((div_le_one (hc (i+1))).mpr (show (c i:ℝ) ≤ c (i+1) from hmono (Nat.le_succ i)))
  have he : (fun x => ((c i:ℝ)/(c (i+1):ℝ))*
      ((c (i+1):ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x)) =
      fun x => (c i:ℝ)*deriv (cascade c h (softAbs M) N (i+1)) x := by
    funext x
    field_simp [ne_of_gt (hc (i+1))]
  rw [he] at hir
  have hh := gaussianBurgers_shape hdatum (cascade_lipschitz hLip c h N (i+1))
    (cascade_even hf hLip (softAbs_even M) c h N (i+1))
    (cascade_curvature_pos hf hLip (softAbs_curvature_pos hMp) c h N (i+1))
    (hc i) hir (sub_nonneg.mpr ht)
  have heq : (fun x => (c i:ℝ)*deriv (finiteValue c h (softAbs M) (N+1) i t) x) =
      gaussianBurgers (c i) (cascade c h (softAbs M) N (i+1)) ((h:ℝ)-t) := by
    rw [finiteValue_head _ c h N i ht]
    rfl
  rwa [heq]

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma RegularDatum.exists_lipschitz {f : ℝ → ℝ} (hf : RegularDatum f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K,hK⟩ := hf.deriv_bounded.bound
  exact ⟨K,lipschitzWith_of_nnnorm_deriv_le (hf.smooth.differentiable (by simp))
    (fun x => NNReal.coe_le_coe.mp (by simpa only [coe_nnnorm,Real.norm_eq_abs] using hK x))⟩

lemma RegularDatum.sub_mul {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : RegularDatum g) (δ : ℝ) :
    RegularDatum (fun x => f x-δ*g x) := by
  refine ⟨hf.smooth.sub (contDiff_const.mul hg.smooth),?_⟩
  have he : deriv (fun x => f x-δ*g x)=fun x => deriv f x+(-δ)*deriv g x := by
    funext x
    convert (((hf.smooth.differentiable (by simp)) x).hasDerivAt.sub
      (((hg.smooth.differentiable (by simp)) x).hasDerivAt.const_mul δ)).deriv using 1 <;> try rfl
    first | rfl | ring
  rw [he]
  exact hf.deriv_bounded.add (hg.deriv_bounded.const_mul (-δ))

lemma forwardBoundary_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) :
    RegularDatum (forwardBoundary c h f N i) := by
  induction i with
  | zero => exact RegularDatum.const _
  | succ i ih =>
    have hφ : RegularDatum (backwardBoundary c h f N (i+1)) := cascade_regular hf hLip c h _ _
    rw [forwardBoundary]
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact (RegularDatum.const _).sub_mul hφ _
    · simp only [hi,ite_false]
      obtain ⟨K,hK⟩ := ih.exists_lipschitz
      exact (forwardCorrection_regular (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) hh) ih hK h).sub_mul hφ _

lemma backwardBoundary_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) :
    BackwardShape (fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x) :=
  cascade_backward_shape c hc hmono hM h _ _

lemma backwardBoundary_third_nonpos {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (backwardBoundary c h (softAbs M) N i) x ≤ 0 := by
  have hp := (hc 0).trans_le (hM 0)
  have hf : RegularDatum (backwardBoundary c h (softAbs M) N i) :=
    cascade_regular (regularDatum_softAbs (ne_of_gt hp)) (softAbs_lipschitz (ne_of_gt hp)) c h _ _
  have hh := (backwardBoundary_shape c hc hmono hM h N i).second_nonpos x hx
  rw [iteratedDeriv_const_mul_field,← iteratedDeriv_succ'] at hh
  exact nonpos_of_mul_nonpos_right hh (hc i)

lemma forwardBoundary_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) :
    ForwardDatumShape (forwardBoundary c h (softAbs M) N i) := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  induction i with
  | zero => exact ForwardDatumShape.const _
  | succ i ih =>
    have hφ : RegularDatum (backwardBoundary c h (softAbs M) N (i+1)) := cascade_regular hf hLip c h _ _
    have heφ := cascade_even hf hLip (softAbs_even M) c h (N-(i+1)) (i+1)
    have hv : ∀ x, 0 ≤ iteratedDeriv 2 (backwardBoundary c h (softAbs M) N (i+1)) x := by
      intro x
      simpa only [backwardBoundary,iteratedDeriv_succ,iteratedDeriv_zero] using
        (cascade_curvature_pos hf hLip (softAbs_curvature_pos hp) c h (N-(i+1)) (i+1) x).le
    have hw := backwardBoundary_third_nonpos c hc hmono hM h N (i+1)
    have hδ : 0 ≤ (c (i+1):ℝ)-(c i:ℝ) := sub_nonneg.mpr (hmono (Nat.le_succ i))
    rw [forwardBoundary]
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact ForwardDatumShape.jump contDiff_const hφ.smooth (ForwardDatumShape.const _) heφ hv hw hδ
    · simp only [hi,ite_false]
      have hr := forwardBoundary_regular hf hLip c hh N i
      obtain ⟨K,hK⟩ := hr.exists_lipschitz
      have ha := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)) hh
      exact ForwardDatumShape.jump (forwardCorrection_smooth hr hK h) hφ.smooth
        (forwardCorrection_shape ha hr hK ih h.coe_nonneg) heφ hv hw hδ

end ZeroTemperatureSK.Heat

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
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.Certificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ZeroTemperatureSK.Certificate
noncomputable section

theorem rational_identity (R K v b j z L : ℝ) :
    z^2 - 12*R*v*b^2 + 6*v^4 =
      (z+Q R K v b)^2 + (z+b*v-2*R*b)*T R v j +
      weightedSquares R K v b (b-2*v) j + WF₂ R K v b j z L +
      L*(x₀*v^2+h*b*v) + remainder R K v (b-2*v) j := by
  unfold Q T weightedSquares P₀ P₁ P₂ P₃ P₄ WF₂ DF₂ F₂R F₂K F₂v F₂b F₂j F₂ F₁
  unfold Q T remainder A C k T₀ g₀ h x₀ y m n₀
  ring

theorem hasDerivAt_F₂ {R K v b j : ℝ → ℝ} {R' K' v' b' j' x : ℝ}
    (hR : HasDerivAt R R' x) (hK : HasDerivAt K K' x)
    (hv : HasDerivAt v v' x) (hb : HasDerivAt b b' x) (hj : HasDerivAt j j' x) :
    HasDerivAt (fun t => F₂ (R t) (K t) (v t) (b t) (j t))
      (R' * F₂R (R x) (K x) (v x) (b x) (j x) +
       K' * F₂K (R x) (K x) (v x) (b x) (j x) +
       v' * F₂v (R x) (K x) (v x) (b x) (j x) +
       b' * F₂b (R x) (K x) (v x) (b x) (j x) +
       j' * F₂j (R x) (K x) (v x) (b x) (j x)) x := by
  have hM := ((hR.const_mul 2).mul_const k).sub (hv.const_mul A)
  have hN := ((((((hK.const_mul (-2)).mul_const k).mul hv).sub
    ((hR.mul_const g₀).mul hv)).sub (((hR.const_mul 2).mul_const T₀).mul hv)).sub
    ((hv.pow 2).const_mul (2*C))).sub ((hj.const_mul h).mul hv)
  have hF₁ := ((hb.pow 2).mul hM).add (hb.mul hN)
  have hF₂ := ((((((hv.pow 2).const_mul x₀).mul hj).add ((hv.pow 3).const_mul y)).add
    ((hK.const_mul m).mul (hv.pow 2))).add ((hR.const_mul n₀).mul (hv.pow 2))).sub hF₁
  convert! hF₂ using 1 <;> try rfl
  simp only [F₂R, F₂K, F₂v, F₂b, F₂j, Q, T,
    Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  ring

theorem remainder_lower_bound {R K v B j : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hv : 0 ≤ v) (hB : 0 ≤ B) (hj : 0 ≤ j) :
    (1661507 / 1521000000 : ℝ) * v^4 ≤ remainder R K v B j := by
  unfold remainder
  have hrest : 0 ≤
      223/160000*R^2*v^2 + 4007/240000*R^2*v*B + 1097/120000*R^2*B^2 +
      83/80000*R*K*v^2 + 3343/24000*R*K*v*B + 16259/23400000*R*v^3 +
      30179/5460000*R*v^2*B + 26/625*R*v^2*j + 107/15000*R*v*B^2 +
      3/2500*R*v*B*j + 121/32500*R*B^3 + 11/10000*R*B^2*j +
      579/20000*K^2*v^2 + 207/2500*K^2*v*B + 911/975000*K*v^3 +
      349/420000*K*v^2*B + 5011/5000*K*v^2*j + 133/130000*K*v*B^2 +
      87/2500*K*v*B*j + 633799/621075000*v^3*B + 10657/1690000*v^2*B^2 := by
    positivity
  linarith only [hrest]

theorem pointwise_coercivity {R K v b j z L : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hv : 0 ≤ v) (hj : 0 ≤ j)
    (hB : 0 ≤ b - 2*v) (hL : 0 ≤ L) (hS : 0 ≤ z+b*v-2*R*b) :
    (1661507 / 1521000000 : ℝ) * v^4 + WF₂ R K v b j z L ≤
      z^2 - 12*R*v*b^2 + 6*v^4 := by
  have hb : 0 ≤ b := by linarith
  have hT : 0 ≤ T R v j := by unfold T g₀ h; positivity
  have hST : 0 ≤ (z+b*v-2*R*b)*T R v j := mul_nonneg hS hT
  have hsq : 0 ≤ weightedSquares R K v b (b-2*v) j := by
    unfold weightedSquares P₀ P₁ P₂ P₃ P₄
    positivity
  have hcorr : 0 ≤ L*(x₀*v^2+h*b*v) := by unfold x₀ h; positivity
  have hrem := remainder_lower_bound hR hK hv hB hj
  have hid := rational_identity R K v b j z L
  have hz : 0 ≤ (z+Q R K v b)^2 := sq_nonneg _
  linarith only [hST, hsq, hcorr, hrem, hid, hz]

theorem coercivity_constant : (1 / 1000 : ℝ) < 1661507 / 1521000000 := by
  norm_num

theorem hasDerivAt_flux {r s ρ R K v b j : ℝ → ℝ}
    {dR dK dv db dj z L x : ℝ}
    (hr : HasDerivAt r (v x) x)
    (hρ : HasDerivAt ρ ((r x - s x) * ρ x) x)
    (hR : HasDerivAt R dR x) (hK : HasDerivAt K dK x)
    (hv : HasDerivAt v dv x) (hb : HasDerivAt b db x)
    (hj : HasDerivAt j dj x)
    (hRval : R x = (r x)^2) (hKval : K x = r x * s x)
    (hDR : r x*dR = 2*R x*v x)
    (hDK : r x*dK = 2*v x*K x + R x*j x)
    (hDv : r x*dv = -R x*b x)
    (hDb : r x*db = -z-b x*v x)
    (hDj : r x*dj = -j x*v x+K x*b x-L) :
    HasDerivAt (fun t => r t * F₂ (R t) (K t) (v t) (b t) (j t) * ρ t)
      (ρ x * WF₂ (R x) (K x) (v x) (b x) (j x) z L) x := by
  have hF := hasDerivAt_F₂ hR hK hv hb hj
  have hD : r x * (dR * F₂R (R x) (K x) (v x) (b x) (j x) +
      dK * F₂K (R x) (K x) (v x) (b x) (j x) +
      dv * F₂v (R x) (K x) (v x) (b x) (j x) +
      db * F₂b (R x) (K x) (v x) (b x) (j x) +
      dj * F₂j (R x) (K x) (v x) (b x) (j x)) =
      DF₂ (R x) (K x) (v x) (b x) (j x) z L := by
    calc
      _ = (r x*dR) * F₂R (R x) (K x) (v x) (b x) (j x) +
        (r x*dK) * F₂K (R x) (K x) (v x) (b x) (j x) +
        (r x*dv) * F₂v (R x) (K x) (v x) (b x) (j x) +
        (r x*db) * F₂b (R x) (K x) (v x) (b x) (j x) +
        (r x*dj) * F₂j (R x) (K x) (v x) (b x) (j x) := by ring
      _ = _ := by rw [hDR, hDK, hDv, hDb, hDj]; rfl
  convert! (hr.mul hF).mul hρ using 1 <;> try rfl
  simp only [Pi.mul_apply]
  unfold WF₂
  rw [← hD, hRval, hKval]
  ring

open MeasureTheory Filter
open scoped Topology

end
end ZeroTemperatureSK.Certificate

end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.RatioJets
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

lemma burgersRate_spatial_deriv {r : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (x : ℝ) :
    deriv (burgersRate r t) x=(1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x := by
  have hd := ((hasDerivAt_spatialJet hr 2 x).const_mul (1/2:ℝ)).add
    ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hr 1 x))
  have hd' : HasDerivAt (burgersRate r t) ((1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma ratioWronskian_spatial {r s : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (hs : ContDiff ℝ ∞ (s t)) (x : ℝ) :
    HasDerivAt (ratioWronskian r s t)
      (r t x*iteratedDeriv 2 (s t) x-s t x*iteratedDeriv 2 (r t) x) x := by
  convert ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hs 1 x)).sub
    ((hasDerivAt_spatialJet hs 0 x).mul (hasDerivAt_spatialJet hr 1 x)) using 1 <;>
    first | rfl | ((try funext y); simp only [ratioWronskian,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma ratioWronskian_second {r s : ℝ → ℝ → ℝ} {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (hs : ContDiff ℝ ∞ (s t)) (x : ℝ) :
    HasDerivAt (deriv (ratioWronskian r s t))
      (deriv (r t) x*iteratedDeriv 2 (s t) x+r t x*iteratedDeriv 3 (s t) x-
        deriv (s t) x*iteratedDeriv 2 (r t) x-s t x*iteratedDeriv 3 (r t) x) x := by
  have he : deriv (ratioWronskian r s t)=fun y =>
      r t y*iteratedDeriv 2 (s t) y-s t y*iteratedDeriv 2 (r t) y :=
    funext (fun y => (ratioWronskian_spatial hr hs y).deriv)
  rw [he]
  convert ((hasDerivAt_spatialJet hr 0 x).mul (hasDerivAt_spatialJet hs 2 x)).sub
    ((hasDerivAt_spatialJet hs 0 x).mul (hasDerivAt_spatialJet hr 2 x)) using 1 <;>
    first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; ring)

lemma ratioWronskian_time {r s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hrt : HasDerivAt (fun u => r u x) (-burgersRate r t x) t)
    (hvt : HasDerivAt (fun u => deriv (r u) x) (-deriv (burgersRate r t) x) t) :
    HasDerivAt (fun u => ratioWronskian r s u x) (ratioWronskianRate r s t x) t := by
  convert (hrt.mul (hs.time_derivative 1 t ht x)).sub
    ((hs.time_derivative 0 t ht x).mul hvt) using 1 <;>
    first | rfl | ((try funext y); simp only [ratioWronskian,ratioWronskianRate,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma ratioWronskian_equation {r s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ}
    (hr : ContDiff ℝ ∞ (r t)) (x : ℝ) (hne : r t x ≠ 0) :
    ratioWronskianRate r s t x-(1/2:ℝ)*iteratedDeriv 2 (ratioWronskian r s t) x+
      (deriv (r t) x/r t x)*deriv (ratioWronskian r s t) x+
      (deriv (r t) x+deriv (s t) x)*ratioWronskian r s t x =
      r t x*s t x*(2*backwardWronskian r t x/(r t x)^2-
        iteratedDeriv 2 (r t) x-iteratedDeriv 2 (s t) x) := by
  have hxx : iteratedDeriv 2 (ratioWronskian r s t) x =
      deriv (r t) x*iteratedDeriv 2 (s t) x+r t x*iteratedDeriv 3 (s t) x-
        deriv (s t) x*iteratedDeriv 2 (r t) x-s t x*iteratedDeriv 3 (r t) x := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using (ratioWronskian_second hr (hs.family.smooth t) x).deriv
  rw [hxx,(ratioWronskian_spatial hr (hs.family.smooth t) x).deriv]
  simp only [ratioWronskianRate,ratioWronskian,backwardWronskian,
    burgersRate_spatial_deriv hr,hs.rate_deriv,burgersRate,scoreRate]
  field_simp [hne]
  ring

lemma tangent_bound_of_concave_odd {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hzero : r 0=0) (hw : ∀ x, 0 < x → iteratedDeriv 2 r x ≤ 0)
    {x : ℝ} (hx : 0 ≤ x) : x*deriv r x ≤ r x := by
  let F (x : ℝ) := r x-x*deriv r x
  have hd (x : ℝ) : HasDerivAt F (-x*iteratedDeriv 2 r x) x := by
    convert (hasDerivAt_spatialJet hr 0 x).sub ((hasDerivAt_id x).mul (hasDerivAt_spatialJet hr 1 x)) using 1 <;>
      first | rfl | ((try funext y); simp only [F,id_eq,iteratedDeriv_zero,iteratedDeriv_succ,Pi.mul_apply,Pi.sub_apply] <;> ring)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (D := Ici (0:ℝ)) (convex_Ici (0:ℝ))
    (show ContinuousOn F (Ici (0:ℝ)) from (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => ?_)
  · have hh := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
    dsimp [F] at hh
    rw [hzero,zero_mul,sub_zero] at hh
    linarith
  · have hxp : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hxp.le) (hw x hxp)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Parabolic.ReverseBurgers
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

lemma SmoothBurgers.reverse {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r) {H : ℝ} (_ : 0 ≤ H) :
    ReverseBurgers (fun t x => r (H-t) x) H := by
  have hfm : BoundedSmoothFamily (fun t x => r (H-t) x) := by
    simpa only [one_mul] using hr.family.reparam (A := fun t => H-t) (C := fun _ => 1)
      (measurable_const.sub measurable_id) measurable_const (fun _ => by norm_num)
  refine ⟨hfm,?_,?_⟩
  · apply (hr.continuous H).comp
      (f := fun p : ℝ × ℝ => (H-p.1,p.2))
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    intro p hp
    exact ⟨⟨sub_nonneg.mpr hp.1.2,sub_le_self _ hp.1.1⟩,mem_univ _⟩
  · intro n t ht htH x
    have hd := (hr.time_derivative n (H-t) (sub_pos.mpr htH) x).comp t
      ((hasDerivAt_id t).const_sub H)
    convert hd using 1 <;> first | rfl | (simp only [mul_neg,mul_one];rfl)

namespace ReverseBurgers
variable {r : ℝ → ℝ → ℝ} {H : ℝ} (hr : ReverseBurgers r H)
include hr

lemma jet_continuous (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (r p.1) p.2) (Icc (0:ℝ) H ×ˢ univ) :=
  hr.family.continuousOn_iteratedDeriv hr.continuous n

lemma ratio_continuous {s : ℝ → ℝ → ℝ} (hs : SmoothForward s) :
    ContinuousOn (fun p : ℝ × ℝ => ratioWronskian r s p.1 p.2) (Icc (0:ℝ) H ×ˢ univ) := by
  have hv : ContinuousOn (fun p : ℝ × ℝ => deriv (r p.1) p.2) (Icc (0:ℝ) H ×ˢ univ) := by
    simpa only [iteratedDeriv_one] using hr.jet_continuous 1
  exact (hr.continuous.mul hs.family.deriv.continuous.continuousOn).sub
    (hs.family.continuous.continuousOn.mul hv)

lemma ratio_time {s : ℝ → ℝ → ℝ} (hs : SmoothForward s) {t : ℝ} (ht : 0 < t) (htH : t < H) (x : ℝ) :
    HasDerivAt (fun u => ratioWronskian r s u x) (ratioWronskianRate r s t x) t := by
  apply ratioWronskian_time hs ht x
  · simpa only [iteratedDeriv_zero] using hr.time_derivative 0 t ht htH x
  · simpa only [iteratedDeriv_one] using hr.time_derivative 1 t ht htH x

end ReverseBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.RatioComparison
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

lemma BackwardShape.zero {r : ℝ → ℝ} (hr : BackwardShape r) : r 0=0 := by
  have hh := hr.odd 0
  simp only [neg_zero] at hh
  linarith

lemma BackwardShape.pos {r : ℝ → ℝ} (hr : BackwardShape r) {x : ℝ} (hx : 0 < x) :
    0 < r x := by
  simpa only [hr.zero] using strictMono_of_deriv_pos hr.derivative_pos hx

theorem ReverseBurgers.ratio_nonneg_interior {r s : ℝ → ℝ → ℝ} {H : ℝ}
    (hr : ReverseBurgers r H) (hs : SmoothForward s)
    (hshape : ∀ t ∈ Icc (0:ℝ) H, BackwardShape (r t))
    (hso : ∀ t, Function.Odd (s t))
    (hsa : ∀ t, 0 ≤ t → ∀ x, 0 ≤ deriv (s t) x)
    (hsw : ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0)
    (hi : ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s 0 x)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T < H) :
    ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s T x := by
  obtain ⟨R,hR⟩ := hr.family.bound
  obtain ⟨V,hV⟩ := hr.family.deriv.bound
  obtain ⟨A,hA⟩ := hs.deriv_family.bound
  obtain ⟨C,hC,hCs⟩ := hs.family.bound
  have hsz (t : ℝ) : s t 0=0 := by
    have hh := hso t 0
    simp only [neg_zero] at hh
    linarith
  have hsp (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ s t x := by
    have hm := monotone_of_deriv_nonneg ((hs.family.smooth t).differentiable (by simp)) (hsa t ht)
    simpa only [hsz] using hm hx
  have hlow (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : ℝ) (hx : 0 ≤ x) :
      -((R:ℝ)*A+C*((V:ℝ)+R)) ≤ ratioWronskian r s t x := by
    have hrsh := hshape t ⟨ht.1,ht.2.trans hTH.le⟩
    have hv : 0 ≤ deriv (r t) x := (hrsh.derivative_pos x).le
    have hvb : deriv (r t) x ≤ V := (le_abs_self _).trans (hV t x)
    have htangent := tangent_bound_of_concave_odd (hr.family.regular t).smooth hrsh.zero
      (fun _ hy => hrsh.second_nonpos _ hy.le) hx
    have hrb : r t x ≤ R := (le_abs_self _).trans (hR t x)
    have hsb : s t x ≤ C*(1+x) := by
      simpa only [abs_of_nonneg hx] using (le_abs_self _).trans (hCs t x)
    have hp1 : -((R:ℝ)*A) ≤ r t x*deriv (s t) x := by
      have hh := mul_le_mul (hR t x) (hA t x) (abs_nonneg _) R.coe_nonneg
      rw [← abs_mul] at hh
      exact (neg_le_neg hh).trans (neg_abs_le _)
    have hp2 : s t x*deriv (r t) x ≤ C*((V:ℝ)+R) := by
      have hh := mul_le_mul_of_nonneg_right hsb hv
      have hh₂ := mul_le_mul_of_nonneg_left (show (1+x)*deriv (r t) x ≤ (V:ℝ)+R by nlinarith) hC
      nlinarith
    dsimp [ratioWronskian]
    linarith
  intro x hx
  apply Parabolic.nonnegative_halfLine_bounded
    (u := ratioWronskian r s) (ut := ratioWronskianRate r s)
    (ux := fun t => deriv (ratioWronskian r s t))
    (uxx := fun t => iteratedDeriv 2 (ratioWronskian r s t))
    (β := fun t x => -(deriv (r t) x/r t x))
    (c := fun t x => -(deriv (r t) x+deriv (s t) x)) (C := 0) (K := 0)
    (M := (R:ℝ)*A+C*((V:ℝ)+R)) (by norm_num) (by positivity)
    ((hr.ratio_continuous hs).mono (by intro p hp;exact ⟨⟨hp.1.1,hp.1.2.trans hTH.le⟩,mem_univ _⟩))
    (fun t _ => (((hr.family.regular t).smooth.continuous.mul (hs.deriv_family.regular t).smooth.continuous).sub
      ((hs.family.smooth t).continuous.mul (hr.family.deriv.regular t).smooth.continuous)))
    (fun t ht x _ => (hr.ratio_time hs ht.1 (ht.2.trans_lt hTH) x).hasDerivWithinAt)
    (fun t _ x _ => by
      rw [(ratioWronskian_spatial (hr.family.regular t).smooth (hs.family.smooth t) x).deriv]
      exact ratioWronskian_spatial (hr.family.regular t).smooth (hs.family.smooth t) x)
    (fun t _ x _ => by
      convert ratioWronskian_second (hr.family.regular t).smooth (hs.family.smooth t) x using 1 <;> try rfl
      rw [iteratedDeriv_succ,iteratedDeriv_one,
        (ratioWronskian_second (hr.family.regular t).smooth (hs.family.smooth t) x).deriv])
    (fun t ht x hx => ?_) (fun t ht x _ => ?_) (fun t ht x hx => ?_)
    hlow hi (fun t ht => ?_) T ⟨hT,le_rfl⟩ x hx
  · have hrsh := hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩
    simpa only [zero_mul] using mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (hrsh.derivative_pos x).le (hrsh.pos hx).le)) hx.le
  · exact neg_nonpos.mpr (add_nonneg
      (hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩ |>.derivative_pos x |>.le) (hsa t ht.1.le x))
  · have hrsh := hshape t ⟨ht.1.le,ht.2.trans hTH.le⟩
    have he := ratioWronskian_equation hs (hr.family.regular t).smooth x (ne_of_gt (hrsh.pos hx))
    have hk : 0 ≤ backwardWronskian r t x := hrsh.wronskian_nonneg x hx.le
    have hnon : 0 ≤ r t x*s t x*(2*backwardWronskian r t x/(r t x)^2-
        iteratedDeriv 2 (r t) x-iteratedDeriv 2 (s t) x) :=
      mul_nonneg (mul_nonneg (hrsh.pos hx).le (hsp t ht.1.le x hx.le))
        (by have hh := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hk) (sq_nonneg (r t x))
            linarith [hrsh.second_nonpos x hx.le,hsw t ht.1.le x hx.le])
    convert he ▸ hnon using 1 <;> try rfl
    ring
  · dsimp [ratioWronskian]
    rw [(hshape t ⟨ht.1,ht.2.trans hTH.le⟩).zero,hsz]
    simp

theorem ReverseBurgers.ratio_nonneg {r s : ℝ → ℝ → ℝ} {H : ℝ}
    (hr : ReverseBurgers r H) (hs : SmoothForward s)
    (hshape : ∀ t ∈ Icc (0:ℝ) H, BackwardShape (r t))
    (hso : ∀ t, Function.Odd (s t))
    (hsa : ∀ t, 0 ≤ t → ∀ x, 0 ≤ deriv (s t) x)
    (hsw : ∀ t, 0 ≤ t → ∀ x, 0 ≤ x → iteratedDeriv 2 (s t) x ≤ 0)
    (hi : ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s 0 x)
    {T : ℝ} (hT : T ∈ Icc (0:ℝ) H) :
    ∀ x, 0 ≤ x → 0 ≤ ratioWronskian r s T x := by
  intro x hx
  by_cases hTH : T < H
  · exact hr.ratio_nonneg_interior hs hshape hso hsa hsw hi hT.1 hTH x hx
  have he : T=H := le_antisymm hT.2 (le_of_not_gt hTH)
  subst T
  by_cases hH : H=0
  · simpa only [hH] using hi x hx
  have hHp : 0 < H := lt_of_le_of_ne hT.1 (Ne.symm hH)
  have : NeBot (𝓝[Ico (0:ℝ) H] H) := right_nhdsWithin_Ico_neBot hHp
  have hc : ContinuousOn (fun t => ratioWronskian r s t x) (Icc (0:ℝ) H) :=
    (hr.ratio_continuous hs).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht,mem_univ _⟩)
  apply ge_of_tendsto ((hc H ⟨hHp.le,le_rfl⟩).mono Ico_subset_Icc_self)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hr.ratio_nonneg_interior hs hshape hso hsa hsw hi ht.1 ht.2 x hx

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma forwardScore_eq_datumScore {a : ℝ} {L : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    forwardScore a L t=datumScore (a+t) (forwardCorrection a L t) := by
  funext x
  simp only [forwardScore,datumScore,forwardTime,max_eq_left ht]

lemma forwardScore_initial {a : ℝ} (ha : a ≠ 0) (L : ℝ → ℝ) :
    forwardScore a L 0=datumScore a L := by
  rw [forwardScore_eq_datumScore le_rfl,add_zero,forwardCorrection_terminal a ha]

lemma datumScore_deriv {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (a x : ℝ) :
    deriv (datumScore a L) x=1/a-iteratedDeriv 2 L x := by
  have hh := ((hasDerivAt_id x).div_const a).sub (hasDerivAt_spatialJet hL 1 x)
  apply HasDerivAt.deriv
  convert hh using 1 <;> try rfl
  first | rfl | ((try funext y);simp only [datumScore,id_eq,iteratedDeriv_succ,iteratedDeriv_zero,Pi.sub_apply])

lemma datumScore_jump {L φ : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (hφ : ContDiff ℝ ∞ φ) (a δ : ℝ) :
    datumScore a (fun x => L x-δ*φ x)=fun x => datumScore a L x+δ*deriv φ x := by
  funext x
  have hd : deriv (fun x => L x-δ*φ x) x=deriv L x-δ*deriv φ x := by
    apply HasDerivAt.deriv
    convert (((hL.differentiable (by simp)) x).hasDerivAt.sub
      (((hφ.differentiable (by simp)) x).hasDerivAt.const_mul δ)) using 1 <;> try rfl
  rw [datumScore,hd]
  dsimp only [datumScore]
  ring

lemma ratioWronskian_jump {L φ : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (hφ : ContDiff ℝ ∞ φ)
    (a c d x : ℝ) (hc : c ≠ 0) :
    ratioWronskian (fun _ y => d*deriv φ y)
      (fun _ => datumScore a (fun y => L y-(d-c)*φ y)) 0 x =
    d/c*ratioWronskian (fun _ y => c*deriv φ y) (fun _ => datumScore a L) 0 x := by
  have hds : ContDiff ℝ ∞ (datumScore a L) :=
    (contDiff_id.div_const a).sub (contDiff_infty_iff_deriv.mp hL |>.2)
  rw [datumScore_jump hL hφ]
  have hder (k : ℝ) : deriv (fun y => k*deriv φ y) x=k*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_spatialJet hφ 1 x).const_mul k using 1 <;> try rfl
    first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  have hd : deriv (fun y => datumScore a L y+(d-c)*deriv φ y) x =
      deriv (datumScore a L) x+(d-c)*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert ((hds.differentiable (by simp)) x).hasDerivAt.add
      ((hasDerivAt_spatialJet hφ 1 x).const_mul (d-c)) using 1 <;> try rfl
    first | rfl | ((try funext y);simp only [iteratedDeriv_succ,iteratedDeriv_zero,Pi.add_apply])
  dsimp only [ratioWronskian]
  rw [hd,hder,hder]
  field_simp [hc]
  ring

lemma ratioWronskian_first_jump {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a c d C : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hshape : BackwardShape (fun x => d*deriv φ x)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ratioWronskian (fun _ y => d*deriv φ y)
      (fun _ => datumScore a (fun y => C-(d-c)*φ y)) 0 x := by
  rw [ratioWronskian_jump contDiff_const hφ a c d x (ne_of_gt hc)]
  have htan := tangent_bound_of_concave_odd
    (contDiff_const.mul (contDiff_infty_iff_deriv.mp hφ |>.2)) hshape.zero
    (fun y hy => hshape.second_nonpos y hy.le) hx
  have hv : deriv (fun y => d*deriv φ y) x=d*iteratedDeriv 2 φ x := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_spatialJet hφ 1 x).const_mul d using 1 <;> try rfl
    first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hv] at htan
  have ht : 0 ≤ deriv φ x-x*iteratedDeriv 2 φ x := by nlinarith
  have he : ratioWronskian (fun _ y => c*deriv φ y)
      (fun _ => datumScore a (fun _ => C)) 0 x = c/a*(deriv φ x-x*iteratedDeriv 2 φ x) := by
    have hs : datumScore a (fun _ => C)=fun y => y/a := by
      funext y
      simp [datumScore]
    rw [hs]
    have hv' : deriv (fun y => c*deriv φ y) x=c*iteratedDeriv 2 φ x := by
      apply HasDerivAt.deriv
      convert (hasDerivAt_spatialJet hφ 1 x).const_mul c using 1 <;> try rfl
      first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    have hq : deriv (fun y : ℝ => y/a) x=1/a := by
      exact ((hasDerivAt_id x).div_const a).deriv
    dsimp only [ratioWronskian]
    rw [hv',hq]
    ring
  rw [he]
  exact mul_nonneg (div_nonneg hd.le hc.le) (mul_nonneg (div_nonneg hc.le ha.le) ht)

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.FiniteForwardRatio
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

lemma backwardSegment_initial {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    backwardSegment c h f N i 0=fun x => (c i:ℝ)*deriv (backwardBoundary c h f N i) x := by
  have hn : N-i=(N-(i+1))+1 := by omega
  have hφ := (cascade_regular hf hLip c h (N-(i+1)) (i+1)).smooth.continuous.measurable
  have he : varianceLogHeat (c i) (h:ℝ) (backwardBoundary c h f N (i+1)) =
      backwardBoundary c h f N i := by
    funext x
    unfold backwardBoundary
    rw [varianceLogHeat_eq_logSemigroup_toNNReal hφ,Real.toNNReal_coe]
    simp only [hn,cascade]
  change (fun x => (c i:ℝ)*deriv (varianceLogHeat (c i) ((h:ℝ)-0) (backwardBoundary c h f N (i+1))) x)=_
  rw [sub_zero,he]

lemma backwardSegment_terminal (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) :
    backwardSegment c h f N i h=fun x => (c i:ℝ)*deriv (backwardBoundary c h f N (i+1)) x := by
  change (fun x => (c i:ℝ)*deriv (varianceLogHeat (c i) ((h:ℝ)-h) (backwardBoundary c h f N (i+1))) x)=_
  have he : varianceLogHeat (c i) 0 (backwardBoundary c h f N (i+1))=backwardBoundary c h f N (i+1) := by
    funext x
    simpa only [backward,sub_self] using backward_terminal (c i) (h:ℝ) (backwardBoundary c h f N (i+1)) x
  rw [sub_self,he]

lemma backwardSegment_reverse {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : ReverseBurgers (backwardSegment c h f N i) h :=
  (gaussianBurgers_smooth (cascade_regular hf hLip c h _ _)
    (cascade_lipschitz hLip c h _ _) (c i).coe_nonneg).reverse h.coe_nonneg

lemma backwardSegment_shape {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    (h : ℝ≥0) (N i : ℕ) {t : ℝ} (ht : t ≤ h) :
    BackwardShape (backwardSegment c h (softAbs M) N i t) := by
  have hh := finiteHead_backward_shape c hc hmono hM h (N-(i+1)) i t ht
  rw [finiteValue_head _ c h _ i ht] at hh
  exact hh

lemma forwardSegment_ratio {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi0 : 0 < i) (hiN : i < N)
    (hi : ∀ x, 0 ≤ x → 0 ≤ boundaryRatio c h (softAbs M) N i x)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) h) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ratioWronskian (backwardSegment c h (softAbs M) N i)
      (forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i)) t x := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  have hL := forwardBoundary_regular hf hLip c hh N i
  obtain ⟨K,hK⟩ := hL.exists_lipschitz
  have ha := mul_pos (Nat.cast_pos.mpr hi0) hh
  have hshape := forwardBoundary_shape c hc hmono hM hh N i
  have hs := forwardScore_smooth ha hL hK
  apply (backwardSegment_reverse hf hLip c h N i).ratio_nonneg hs
    (fun τ hτ => backwardSegment_shape c hc hmono hM h N i hτ.2)
    (forwardScore_odd hL hK hshape.even) (fun τ hτ y => ?_) (fun τ hτ y hy => ?_)
    (fun y hy => ?_) ht x hx
  · rw [forwardScore_deriv hL hK]
    have h₂ := (forwardCorrection_shape ha hL hK hshape hτ).second y
    have hb := inv_pos.mpr (forwardTime_pos ha τ)
    linarith
  · rw [forwardScore_second hL hK]
    exact neg_nonpos.mpr ((forwardCorrection_shape ha hL hK hshape hτ).third y hy)
  · have hh := hi y hy
    change 0 ≤ (backwardSegment c h (softAbs M) N i 0 y)*
      deriv (forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) 0) y-
      forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) 0 y*
      deriv (backwardSegment c h (softAbs M) N i 0) y
    rw [backwardSegment_initial hf hLip c h hiN,forwardScore_initial (ne_of_gt ha)]
    exact hh

theorem boundaryRatio_nonneg {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) (hi0 : 0 < i) (hiN : i ≤ N) :
    ∀ x, 0 ≤ x → 0 ≤ boundaryRatio c h (softAbs M) N i x := by
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  induction i with
  | zero => omega
  | succ i ih =>
    intro x hx
    by_cases hi : i=0
    · subst i
      have hφ := (cascade_regular hf hLip c h (N-1) 1).smooth
      have hs := backwardBoundary_shape c hc hmono hM h N 1
      simpa only [boundaryRatio,forwardBoundary,ite_true,Nat.zero_add,Nat.cast_one,one_mul,backwardBoundary] using
        ratioWronskian_first_jump hφ hh (hc 0) (hc 1) (C := -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-
          (c 0:ℝ)*backwardBoundary c h (softAbs M) N 0 0) hs hx
    · have hi0' : 0 < i := Nat.pos_of_ne_zero hi
      have hiN' : i < N := by omega
      have hprev := forwardSegment_ratio c hc hmono hM hh hi0' hiN'
        (ih hi0' hiN'.le) (t := (h:ℝ)) ⟨h.coe_nonneg,le_rfl⟩ x hx
      have hφ : ContDiff ℝ ∞ (backwardBoundary c h (softAbs M) N (i+1)) :=
        (cascade_regular hf hLip c h (N-(i+1)) (i+1)).smooth
      have hL := forwardBoundary_regular hf hLip c hh N i
      obtain ⟨K,hK⟩ := hL.exists_lipschitz
      have he : ((i+1:ℕ):ℝ)*(h:ℝ)=(i:ℝ)*h+h := by push_cast;ring
      change 0 ≤ ratioWronskian (fun _ => backwardSegment c h (softAbs M) N i h)
        (fun _ => forwardScore ((i:ℝ)*h) (forwardBoundary c h (softAbs M) N i) h) 0 x at hprev
      rw [forwardScore_eq_datumScore h.coe_nonneg,backwardSegment_terminal] at hprev
      dsimp only [boundaryRatio]
      simp only [forwardBoundary,ite_eq_right hi,he]
      rw [ratioWronskian_jump (forwardCorrection_smooth hL hK h) hφ _ _ _ _ (ne_of_gt (hc i))]
      exact mul_nonneg (div_nonneg (hc (i+1)).le (hc i).le) hprev

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma cert_flux_derivative {r s ρ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    {x : ℝ} (hne : r x ≠ 0) (hρ : HasDerivAt ρ ((r x-s x)*ρ x) x) :
    HasDerivAt (certFlux r s ρ) (certDivergence r s ρ x) x := by
  have hr' : HasDerivAt r (certV r x) x := (hr.differentiable (by simp) x).hasDerivAt
  have hv : HasDerivAt (certV r) (certW r x) x := by simpa only [iteratedDeriv_one,certV,certW] using hasDerivAt_spatialJet hr 1 x
  have hw : HasDerivAt (certW r) (certZ r x) x := hasDerivAt_spatialJet hr 2 x
  have hs' : HasDerivAt s (deriv s x) x := (hs.differentiable (by simp) x).hasDerivAt
  have hs'' : HasDerivAt (deriv s) (iteratedDeriv 2 s x) x := by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet hs 1 x
  apply Certificate.hasDerivAt_flux hr' hρ (hr'.pow 2) (hr'.mul hs') hv
    (hw.neg.div hr' hne) (hs''.sub (((hs'.div hr' hne).mul hv))) rfl rfl
  · simp only [Pi.pow_apply];ring
  · dsimp [certK,certR,certJ]
    field_simp [hne]
    ring
  · dsimp [certR,certB]
    field_simp [hne]
  · dsimp [certB]
    field_simp [hne]
  · dsimp [certJ,certK,certB,certL]
    field_simp [hne]
    ring

lemma cert_halfLine_signs {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ certR r x ∧ 0 ≤ certK r s x ∧ 0 ≤ certV r x ∧ 0 ≤ certJ r s x ∧
    0 ≤ certB r x-2*certV r x ∧ 0 ≤ certL r s x ∧
    0 ≤ certZ r x+certB r x*certV r x-2*certR r x*certB r x := by
  have hp := hshape.pos hx
  have hn := ne_of_gt hp
  have hs0 : s 0=0 := by have hh := hso 0;simp only [neg_zero] at hh;linarith
  have hsp : 0 ≤ s x := by
    simpa only [hs0] using (monotone_of_deriv_nonneg (hs.differentiable (by simp)) hsa hx.le)
  refine ⟨sq_nonneg _,mul_nonneg hp.le hsp,(hshape.derivative_pos x).le,?_,?_,?_,?_⟩
  · have he : certJ r s x=(r x*deriv s x-s x*deriv r x)/r x := by
      dsimp [certJ,certV]
      field_simp
    rw [he]
    exact div_nonneg (hQ x hx.le) hp.le
  · have he : certB r x-2*certV r x= -2*burgersRate (fun _ => r) 0 x/r x := by
      dsimp [certB,certW,certV,burgersRate]
      field_simp [hn]
      ring
    rw [he]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hshape.rate_nonpos x hx.le)) hp.le
  · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp.le) (hsw x hx.le)
  · have he : certZ r x+certB r x*certV r x-2*certR r x*certB r x=
        2*backwardWronskian (fun _ => r) 0 x/r x := by
      rw [backwardWronskian,burgersRate_spatial_deriv hr]
      dsimp [certZ,certB,certW,certV,certR,burgersRate]
      field_simp [hn]
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (by norm_num) (hshape.wronskian_nonneg x hx.le)) hp.le

lemma cert_halfLine_coercive {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    {x : ℝ} (hx : 0 < x) :
    (1661507/1521000000:ℝ)*(certV r x)^4+
      Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
        (certZ r x) (certL r s x) ≤
      (certZ r x)^2-12*certV r x*(certW r x)^2+6*(certV r x)^4 := by
  obtain ⟨hR,hK,hv,hj,hB,hL,hS⟩ := cert_halfLine_signs hr hs hshape hso hsa hsw hQ hx
  have he : certR r x*(certB r x)^2=(certW r x)^2 := by
    dsimp [certR,certB]
    field_simp [ne_of_gt (hshape.pos hx)]
  have hh := Certificate.pointwise_coercivity hR hK hv hj hB hL hS
  rw [show 12*certR r x*certV r x*(certB r x)^2=12*certV r x*(certR r x*(certB r x)^2) by ring,he] at hh
  exact hh

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.GaussianDecay
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

lemma linear_abs_le_quadratic {d : ℝ} (hd : 0 < d) (K x : ℝ) :
    K*|x| ≤ d/2*x^2+K^2/(2*d) := by
  apply (mul_le_mul_iff_of_pos_left (show (0:ℝ)<2*d by positivity)).mp
  have he : (2*d)*(d/2*x^2+K^2/(2*d))=d^2*x^2+K^2 := by field_simp
  rw [he]
  have hs : 0 ≤ d^2*x^2-2*d*K*|x|+K^2 := by
    have heq : d^2*x^2-2*d*K*|x|+K^2=(d*|x|-K)^2 := by
      rw [sub_sq,mul_pow,sq_abs]
      ring
    rw [heq]
    exact sq_nonneg _
  nlinarith only [hs]

lemma integrable_gaussian_linear {d : ℝ} (hd : 0 < d) (K : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-d*x^2+K*|x|)) := by
  apply ((integrable_exp_neg_mul_sq (half_pos hd)).const_mul (Real.exp (K^2/(2*d)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := linear_abs_le_quadratic hd K x
  linarith

lemma integrable_gaussian_expBound {g : ℝ → ℝ} (hgm : Measurable g) (hg : ExponentialBound g)
    {d : ℝ} (hd : 0 < d) : Integrable (fun x => Real.exp (-d*x^2)*g x) := by
  obtain ⟨A,K,hA⟩ := hg
  apply ((integrable_gaussian_linear hd K).const_mul (A:ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-d*x^2)*|g x| ≤ Real.exp (-d*x^2)*((A:ℝ)*Real.exp ((K:ℝ)*|x|)) :=
      mul_le_mul_of_nonneg_left (hA x) (Real.exp_nonneg _)
    _ = (A:ℝ)*Real.exp (-d*x^2+(K:ℝ)*|x|) := by rw [Real.exp_add];ring

lemma ExponentialBound.mul {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x*g x) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  refine ⟨A*B,K+J,fun x => ?_⟩
  rw [abs_mul]
  calc
    |f x| * |g x| ≤ ((A:ℝ)*Real.exp ((K:ℝ)*|x|))*((B:ℝ)*Real.exp ((J:ℝ)*|x|)) :=
      mul_le_mul (hA x) (hB x) (abs_nonneg _) (by positivity)
    _ = ((A*B:ℝ≥0):ℝ)*Real.exp (((K+J:ℝ≥0):ℝ)*|x|) := by
      simp only [NNReal.coe_mul,NNReal.coe_add,add_mul,Real.exp_add]
      ring

lemma gaussian_convolution_quadratic {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x y : ℝ) :
    (1/(8*(a+t)))*(x^2+y^2) ≤ x^2/(2*a)+(y-x)^2/(2*t) := by
  have hs := add_pos ha ht
  have h1 : 1/(2*(a+t)) ≤ 1/(2*a) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1/(2*(a+t)) ≤ 1/(2*t) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hq : x^2+y^2 ≤ 4*(x^2+(y-x)^2) := by nlinarith [sq_nonneg (y-2*x),sq_nonneg x]
  calc
    _ ≤ (1/(8*(a+t)))*(4*(x^2+(y-x)^2)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (1/(2*(a+t)))*x^2+(1/(2*(a+t)))*(y-x)^2 := by
      field_simp
      ring
    _ ≤ (1/(2*a))*x^2+(1/(2*t))*(y-x)^2 := add_le_add
      (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    _ = _ := by ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma continuous_dslope_zero {f : ℝ → ℝ} (hf : Differentiable ℝ f) : Continuous (dslope f 0) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x;exact continuousAt_dslope_same.mpr (hf 0)
  · exact (continuousAt_dslope_of_ne hx).mpr (hf x).continuousAt

lemma BackwardShape.nonzero {r : ℝ → ℝ} (hr : BackwardShape r) {x : ℝ} (hx : x ≠ 0) : r x ≠ 0 := by
  intro he
  exact hx ((strictMono_of_deriv_pos hr.derivative_pos).injective (he.trans hr.odd.map_zero.symm))

lemma BackwardShape.dslope_nonzero {r : ℝ → ℝ} (hr : BackwardShape r) (x : ℝ) : dslope r 0 x ≠ 0 := by
  by_cases hx : x=0
  · subst x;simpa only [dslope_same] using ne_of_gt (hr.derivative_pos 0)
  · simp only [dslope_of_ne r hx,slope,vsub_eq_sub,sub_zero,hr.odd.map_zero,smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hx) (hr.nonzero hx)

lemma quotientExtension_continuous {g r : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) : Continuous (quotientExtension g r) :=
  (continuous_dslope_zero hg).div (continuous_dslope_zero hr) hshape.dslope_nonzero

lemma quotientExtension_eq {g r : ℝ → ℝ} (hg0 : g 0=0) (hr0 : r 0=0) {x : ℝ} (hx : x ≠ 0) :
    quotientExtension g r x=g x/r x := by
  dsimp [quotientExtension]
  simp only [dslope_of_ne _ hx,slope,vsub_eq_sub,hg0,hr0,sub_zero,smul_eq_mul]
  field_simp

lemma BackwardShape.abs_eq {r : ℝ → ℝ} (hr : BackwardShape r) (x : ℝ) : |r x|=r |x| := by
  have hm := (strictMono_of_deriv_pos hr.derivative_pos).monotone
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,abs_of_nonneg (by simpa only [hr.odd.map_zero] using hm hx)]
  · have hxn : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hxn,abs_of_nonpos (by simpa only [hr.odd.map_zero] using hm hxn),hr.odd]

lemma quotient_linear_bound {g r : ℝ → ℝ} {K : ℝ≥0}
    (hg : Differentiable ℝ g) (hLip : LipschitzWith K g) (hg0 : g 0=0)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) :
    ∃ C : ℝ≥0, ∀ x, |g x/r x| ≤ (C:ℝ)*(1+|x|) := by
  have hq := quotientExtension_continuous hg hr hshape
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).bddAbove_image hq.abs.continuousOn
  let C := Real.toNNReal (|R|+(K:ℝ)/r 1)
  have hr1 : 0 < r 1 := by
    simpa only [hshape.odd.map_zero] using
      strictMono_of_deriv_pos hshape.derivative_pos (by norm_num : (0:ℝ)<1)
  have hCR : R ≤ (C:ℝ) := (le_abs_self R).trans ((le_add_of_nonneg_right (div_nonneg K.coe_nonneg hr1.le)).trans (Real.le_coe_toNNReal _))
  have hCK : (K:ℝ)/r 1 ≤ (C:ℝ) := (le_add_of_nonneg_left (abs_nonneg R)).trans (Real.le_coe_toNNReal _)
  refine ⟨C,fun x => ?_⟩
  by_cases hx : x=0
  · subst x;simp only [hg0,zero_div,abs_zero,add_zero,mul_one];exact C.coe_nonneg
  by_cases hsmall : |x| ≤ 1
  · have hmem : x ∈ Icc (-1:ℝ) 1 := abs_le.mp hsmall
    have hb : |quotientExtension g r x| ≤ R := hR ⟨x,hmem,rfl⟩
    rw [quotientExtension_eq hg0 hshape.odd.map_zero hx] at hb
    exact (hb.trans hCR).trans (le_mul_of_one_le_right C.coe_nonneg (by linarith [abs_nonneg x]))
  · have hden : r 1 ≤ |r x| := by
      rw [hshape.abs_eq]
      exact (strictMono_of_deriv_pos hshape.derivative_pos).monotone (le_of_lt (lt_of_not_ge hsmall))
    have hnum : |g x| ≤ (K:ℝ)*|x| := by simpa only [Real.norm_eq_abs,hg0,sub_zero] using hLip.norm_sub_le x 0
    rw [abs_div]
    calc
      |g x|/|r x| ≤ ((K:ℝ)*|x|)/|r x| := div_le_div_of_nonneg_right hnum (abs_nonneg _)
      _ ≤ ((K:ℝ)*|x|)/r 1 := div_le_div_of_nonneg_left (by positivity) hr1 hden
      _ = ((K:ℝ)/r 1)*|x| := by ring
      _ ≤ (C:ℝ)*|x| := mul_le_mul_of_nonneg_right hCK (abs_nonneg x)
      _ ≤ (C:ℝ)*(1+|x|) := by nlinarith [C.coe_nonneg]

lemma exponentialBound_of_linear_bound {g : ℝ → ℝ} {C : ℝ≥0}
    (hC : ∀ x, |g x| ≤ (C:ℝ)*(1+|x|)) : ExponentialBound g := by
  refine ⟨C,1,fun x => ?_⟩
  simp only [NNReal.coe_one,one_mul]
  exact (hC x).trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp |x|) C.coe_nonneg)

lemma exponentialBound_quotient {g r : ℝ → ℝ} {K : ℝ≥0}
    (hg : Differentiable ℝ g) (hLip : LipschitzWith K g) (hg0 : g 0=0)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) : ExponentialBound (fun x => g x/r x) := by
  obtain ⟨C,hC⟩ := quotient_linear_bound hg hLip hg0 hr hshape
  exact exponentialBound_of_linear_bound hC

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.GaussianTails
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

lemma ExponentialBound.const (a : ℝ) : ExponentialBound (fun _ => a) :=
  ExponentialBound.of_bounded (A := Real.nnabs a) (fun _ => le_rfl)

lemma ExponentialBound.neg {f : ℝ → ℝ} (hf : ExponentialBound f) : ExponentialBound (fun x => -f x) := by
  obtain ⟨A,K,hA⟩ := hf
  exact ⟨A,K,fun x => by simpa only [abs_neg] using hA x⟩

lemma ExponentialBound.add {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x+g x) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  refine ⟨A+B,K+J,fun x => ?_⟩
  simp only [NNReal.coe_add]
  have hk : Real.exp ((K:ℝ)*|x|) ≤ Real.exp (((K:ℝ)+J)*|x|) := by gcongr;exact le_add_of_nonneg_right J.coe_nonneg
  have hj : Real.exp ((J:ℝ)*|x|) ≤ Real.exp (((K:ℝ)+J)*|x|) := by gcongr;exact le_add_of_nonneg_left K.coe_nonneg
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x|)+(B:ℝ)*Real.exp ((J:ℝ)*|x|) := add_le_add (hA x) (hB x)
    _ ≤ ((A:ℝ)+B)*Real.exp (((K:ℝ)+J)*|x|) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hk A.coe_nonneg) (mul_le_mul_of_nonneg_left hj B.coe_nonneg)

lemma ExponentialBound.sub {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x-g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExponentialBound.pow {f : ℝ → ℝ} (hf : ExponentialBound f) (n : ℕ) : ExponentialBound (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using ExponentialBound.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma gaussian_expBound_tendsto_zero {g : ℝ → ℝ} (hg : ExponentialBound g)
    {d : ℝ} (hd : 0 < d) : Tendsto (fun x => Real.exp (-d*x^2)*g x) atTop (𝓝 0) := by
  obtain ⟨A,K,hA⟩ := hg
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have he : Tendsto (fun x : ℝ => Real.exp (-(d/2)*x^2)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop (half_pos hd))) using 1 <;> try rfl
    first | rfl | (funext x;dsimp only [Function.comp_apply];congr 1;ring)
  have hlim := he.const_mul ((A:ℝ)*Real.exp ((K:ℝ)^2/(2*d)))
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm _ hlim
  intro x
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-d*x^2)*|g x| ≤ Real.exp (-d*x^2)*((A:ℝ)*Real.exp ((K:ℝ)*|x|)) :=
      mul_le_mul_of_nonneg_left (hA x) (Real.exp_nonneg _)
    _ = (A:ℝ)*Real.exp (-d*x^2+(K:ℝ)*|x|) := by rw [Real.exp_add];ring
    _ ≤ (A:ℝ)*Real.exp (((K:ℝ)^2/(2*d)) + (-(d/2)*x^2)) := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      apply Real.exp_le_exp.mpr
      linarith [linear_abs_le_quadratic hd (K:ℝ) x]
    _ = _ := by rw [Real.exp_add];ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmooth.regular {r : ℝ → ℝ} (hr : BoundedSmooth r) : RegularDatum r := ⟨hr.smooth,hr.deriv⟩

lemma BoundedSmooth.exponentialBound {r : ℝ → ℝ} (hr : BoundedSmooth r) : ExponentialBound r := by
  obtain ⟨C,hC⟩ := hr.bound
  exact ExponentialBound.of_bounded hC

lemma certW_odd {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Odd (certW r) := by
  simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using
    even_deriv_odd ((contDiff_infty_iff_deriv.mp hr |>.2).differentiable (by simp))
      (odd_deriv_even (hr.differentiable (by simp)) ho)

lemma certV_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (certV r) :=
  odd_deriv_even (hr.differentiable (by simp)) ho

lemma certZ_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (certZ r) := by
  have hh := odd_deriv_even ((contDiff_iteratedDeriv_infty hr 2).differentiable (by simp)) (certW_odd hr ho)
  simpa only [certZ,certW,iteratedDeriv_succ] using hh

lemma odd_zero {r : ℝ → ℝ} (ho : Function.Odd r) : r 0=0 := by
  have hh := ho 0
  simp only [neg_zero] at hh
  linarith

lemma cert_flux_continuous {r s ρ : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hshape : BackwardShape r) (hso : Function.Odd s) (hρ : Continuous ρ) : Continuous (certFlux r s ρ) := by
  have hw := contDiff_iteratedDeriv_infty hr 2
  have hbw := quotientExtension_continuous (hw.differentiable (by simp)) (hr.differentiable (by simp)) hshape
  have hbs := quotientExtension_continuous (hs.differentiable (by simp)) (hr.differentiable (by simp)) hshape
  have hv : Continuous (certV r) := (contDiff_infty_iff_deriv.mp hr |>.2).continuous
  have hsd : Continuous (deriv s) := (contDiff_infty_iff_deriv.mp hs |>.2).continuous
  have he : certFlux r s ρ = fun x => r x*Certificate.F₂ (certR r x) (certK r s x) (certV r x)
      (-quotientExtension (certW r) r x) (deriv s x-quotientExtension s r x*certV r x)*ρ x := by
    funext x
    by_cases hx : x=0
    · subst x;simp only [certFlux,hshape.zero,zero_mul]
    · rw [quotientExtension_eq (odd_zero (certW_odd hr hshape.odd)) hshape.zero hx,
        quotientExtension_eq (odd_zero hso) hshape.zero hx]
      simp only [certFlux,certB,certJ,neg_div]
  rw [he]
  dsimp only [Certificate.F₂,Certificate.F₁,certR,certK]
  fun_prop

lemma certificate_growth {r s : ℝ → ℝ} (hr : BoundedSmooth r) (hs : RegularDatum s)
    (hshape : BackwardShape r) (hso : Function.Odd s) :
    ExponentialBound (fun x => Certificate.F₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)) ∧
    ExponentialBound (fun x => Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
      (certZ r x) (certL r s x)) := by
  obtain ⟨K,hK⟩ := hs.exists_lipschitz
  have hsE := exponentialBound_of_lipschitz hK
  have hrE := hr.exponentialBound
  have hR : ExponentialBound (certR r) := hrE.pow 2
  have hKv : ExponentialBound (certK r s) := hrE.mul hsE
  have hv : ExponentialBound (certV r) := hr.deriv.exponentialBound
  have hw : BoundedSmooth (certW r) := by simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv
  obtain ⟨J,hJ⟩ := hw.regular.exists_lipschitz
  have hbe := exponentialBound_quotient (hw.smooth.differentiable (by simp)) hJ
    (odd_zero (certW_odd hr.smooth hshape.odd)) (hr.smooth.differentiable (by simp)) hshape
  have hb : ExponentialBound (certB r) := by
    unfold certB
    simpa only [neg_div] using hbe.neg
  have hse := exponentialBound_quotient (hs.smooth.differentiable (by simp)) hK (odd_zero hso)
    (hr.smooth.differentiable (by simp)) hshape
  have hj : ExponentialBound (certJ r s) := hs.deriv_bounded.exponentialBound.sub (hse.mul hv)
  have hz : ExponentialBound (certZ r) := by
    simpa only [certZ,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv.deriv.exponentialBound
  have hL : ExponentialBound (certL r s) := by
    unfold certL
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hrE.neg.mul hs.deriv_bounded.deriv.exponentialBound
  constructor
  · dsimp only [Certificate.F₂,Certificate.F₁]
    repeat' first | assumption | apply ExponentialBound.add | apply ExponentialBound.sub |
      apply ExponentialBound.mul | apply ExponentialBound.neg | apply ExponentialBound.pow | exact ExponentialBound.const _
  · dsimp only [Certificate.WF₂,Certificate.DF₂,Certificate.F₂R,Certificate.F₂K,Certificate.F₂v,
      Certificate.F₂b,Certificate.F₂j,Certificate.F₂,Certificate.F₁,Certificate.Q,Certificate.T]
    repeat' first | assumption | apply ExponentialBound.add | apply ExponentialBound.sub |
      apply ExponentialBound.mul | apply ExponentialBound.neg | apply ExponentialBound.pow | exact ExponentialBound.const _

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.GaussianLogDensity
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

lemma gaussianLogDensity_continuous {U : ℝ → ℝ} (hU : Continuous U) (d : ℝ) :
    Continuous (gaussianLogDensity d U) := by unfold gaussianLogDensity;fun_prop

lemma gaussianLogDensity_pos (d : ℝ) (U : ℝ → ℝ) (x : ℝ) : 0 < gaussianLogDensity d U x := Real.exp_pos _

lemma gaussianLogDensity_even {U : ℝ → ℝ} (hU : Function.Even U) (d : ℝ) :
    Function.Even (gaussianLogDensity d U) := by intro x;simp only [gaussianLogDensity,neg_sq,hU x]

lemma gaussianLogDensity_derivative {U : ℝ → ℝ} {d x U' : ℝ} (hU : HasDerivAt U U' x) :
    HasDerivAt (gaussianLogDensity d U) ((U'-2*d*x)*gaussianLogDensity d U x) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul (-d) |>.add hU).exp using 1 <;>
    first | rfl | (dsimp [gaussianLogDensity];ring)

lemma gaussianLogDensity_integrable_mul {U g : ℝ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    (hgm : Measurable g) (hg : ExponentialBound g) {d : ℝ} (hd : 0 < d) :
    Integrable (fun x => gaussianLogDensity d U x*g x) := by
  have hE : ExponentialBound (fun x => Real.exp (U x)) := by simpa only [one_mul] using exponentialBound_exp hU 1
  have hh := integrable_gaussian_expBound (hU.continuous.measurable.exp.mul hgm) (hE.mul hg) hd
  simpa only [gaussianLogDensity,Real.exp_add,mul_assoc,Pi.mul_apply] using hh

lemma gaussianLogDensity_tendsto_mul {U g : ℝ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    (hg : ExponentialBound g) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x => gaussianLogDensity d U x*g x) atTop (𝓝 0) := by
  have hE : ExponentialBound (fun x => Real.exp (U x)) := by simpa only [one_mul] using exponentialBound_exp hU 1
  simpa only [gaussianLogDensity,Real.exp_add,mul_assoc,Pi.mul_apply] using gaussian_expBound_tendsto_zero (hE.mul hg) hd

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmooth.pow {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) : BoundedSmooth (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmooth.const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma quarticMoment_boundedSmooth {r : ℝ → ℝ} (hr : BoundedSmooth r) : BoundedSmooth (quarticMoment r) := hr.deriv.pow 4

lemma coercivePolynomial_boundedSmooth {r : ℝ → ℝ} (hr : BoundedSmooth r) : BoundedSmooth (coercivePolynomial r) := by
  have hw : BoundedSmooth (certW r) := by simpa only [certW,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv
  have hz : BoundedSmooth (certZ r) := by simpa only [certZ,iteratedDeriv_succ,iteratedDeriv_zero] using hr.deriv.deriv.deriv
  convert ((hz.pow 2).add ((hr.deriv.mul (hw.pow 2)).const_mul (-12))).add ((hr.deriv.pow 4).const_mul 6) using 1 <;> try rfl
  funext x
  dsimp [coercivePolynomial,certV]
  ring

lemma quarticMoment_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (quarticMoment r) := by
  intro x;simp only [quarticMoment,certV_even hr ho x]

lemma coercivePolynomial_even {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (ho : Function.Odd r) : Function.Even (coercivePolynomial r) := by
  intro x
  simp only [coercivePolynomial,certV_even hr ho x,certZ_even hr ho x,certW_odd hr ho x,neg_sq]

lemma integral_even_two_Ioi {f : ℝ → ℝ} (hf : Function.Even f) : (∫ x, f x)=2*∫ x in Ioi (0:ℝ), f x := by
  have he : (fun x => f |x|)=f := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hx)),hf x]
  have hh := integral_comp_abs (f := f)
  rw [he] at hh
  exact hh

lemma certificate_polynomial_measurable {r s : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s) :
    Measurable (fun x => Certificate.WF₂ (certR r x) (certK r s x) (certV r x) (certB r x) (certJ r s x)
      (certZ r x) (certL r s x)) := by
  have hrm := hr.continuous.measurable
  have hsm := hs.continuous.measurable
  have hvm : Measurable (certV r) := (contDiff_infty_iff_deriv.mp hr |>.2).continuous.measurable
  have hwm : Measurable (certW r) := (contDiff_iteratedDeriv_infty hr 2).continuous.measurable
  have hzm : Measurable (certZ r) := (contDiff_iteratedDeriv_infty hr 3).continuous.measurable
  have hsdm : Measurable (deriv s) := (contDiff_infty_iff_deriv.mp hs |>.2).continuous.measurable
  have hssm : Measurable (iteratedDeriv 2 s) := (contDiff_iteratedDeriv_infty hs 2).continuous.measurable
  have hR : Measurable (certR r) := hrm.pow_const 2
  have hK : Measurable (certK r s) := hrm.mul hsm
  have hB : Measurable (certB r) := hwm.neg.div hrm
  have hJ : Measurable (certJ r s) := hsdm.sub ((hsm.div hrm).mul hvm)
  have hL : Measurable (certL r s) := hrm.neg.mul hssm
  dsimp only [Certificate.WF₂,Certificate.DF₂,Certificate.F₂R,Certificate.F₂K,Certificate.F₂v,
    Certificate.F₂b,Certificate.F₂j,Certificate.F₂,Certificate.F₁,Certificate.Q,Certificate.T]
  fun_prop

theorem gaussian_shape_coercivity {r s U : ℝ → ℝ} {K : ℝ≥0} {d : ℝ}
    (hr : BoundedSmooth r) (hs : RegularDatum s) (hshape : BackwardShape r)
    (hso : Function.Odd s) (hsa : ∀ x, 0 ≤ deriv s x)
    (hsw : ∀ x, 0 ≤ x → iteratedDeriv 2 s x ≤ 0)
    (hQ : ∀ x, 0 ≤ x → 0 ≤ r x*deriv s x-s x*deriv r x)
    (hU : LipschitzWith K U) (hUe : Function.Even U) (hd : 0 < d)
    (hUd : ∀ x, HasDerivAt U (r x-s x+2*d*x) x) :
    (1/1000:ℝ)*(∫ x, gaussianLogDensity d U x*quarticMoment r x) ≤
      ∫ x, gaussianLogDensity d U x*coercivePolynomial r x := by
  let ρ := gaussianLogDensity d U
  have hρ : Continuous ρ := gaussianLogDensity_continuous hU.continuous d
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => (gaussianLogDensity_pos d U x).le
  have hρe : Function.Even ρ := gaussianLogDensity_even hUe d
  have hρd (x : ℝ) : HasDerivAt ρ ((r x-s x)*ρ x) x := by
    convert gaussianLogDensity_derivative (d := d) (hUd x) using 1 <;> try rfl
    first | rfl | ring
  obtain ⟨hF,hW⟩ := certificate_growth hr hs hshape hso
  have hiV : Integrable (fun x => ρ x*quarticMoment r x) :=
    gaussianLogDensity_integrable_mul hU (quarticMoment_boundedSmooth hr).smooth.continuous.measurable
      (quarticMoment_boundedSmooth hr).exponentialBound hd
  have hiP : Integrable (fun x => ρ x*coercivePolynomial r x) :=
    gaussianLogDensity_integrable_mul hU (coercivePolynomial_boundedSmooth hr).smooth.continuous.measurable
      (coercivePolynomial_boundedSmooth hr).exponentialBound hd
  have hiD : Integrable (certDivergence r s ρ) :=
    gaussianLogDensity_integrable_mul hU (certificate_polynomial_measurable hr.smooth hs.smooth) hW hd
  have htFlux : Tendsto (certFlux r s ρ) atTop (𝓝 0) := by
    unfold certFlux
    have hh := gaussianLogDensity_tendsto_mul hU (hr.exponentialBound.mul hF) hd
    simpa only [certFlux,ρ,Pi.mul_apply,mul_comm,mul_left_comm,mul_assoc] using hh
  have hiZero : (∫ x in Ioi (0:ℝ), certDivergence r s ρ x)=0 := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto
      (cert_flux_continuous hr.smooth hs.smooth hshape hso hρ |>.continuousWithinAt (x := 0))
      (fun x hx => cert_flux_derivative hr.smooth hs.smooth (ne_of_gt (hshape.pos hx)) (hρd x))
      hiD.integrableOn htFlux
    simpa only [certFlux,hshape.zero,zero_mul,sub_zero] using hh
  have hhalf : (1661507/1521000000:ℝ)*(∫ x in Ioi (0:ℝ), ρ x*quarticMoment r x) ≤
      ∫ x in Ioi (0:ℝ), ρ x*coercivePolynomial r x := by
    have hm := integral_mono_ae ((hiV.const_mul (1661507/1521000000:ℝ)).add hiD).integrableOn hiP.integrableOn
      (show ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),
        (1661507/1521000000:ℝ)*(ρ x*quarticMoment r x)+certDivergence r s ρ x ≤ ρ x*coercivePolynomial r x from by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hh := mul_le_mul_of_nonneg_left
            (cert_halfLine_coercive hr.smooth hs.smooth hshape hso hsa hsw hQ hx) (hρpos x)
          dsimp only [quarticMoment,coercivePolynomial,certDivergence]
          nlinarith only [hh])
    simp only [Pi.add_apply] at hm
    rw [integral_add (hiV.const_mul _).integrableOn hiD.integrableOn,integral_const_mul,hiZero,add_zero] at hm
    exact hm
  have hVe : Function.Even (fun x => ρ x*quarticMoment r x) := by
    intro x;dsimp only;rw [hρe x,quarticMoment_even hr.smooth hshape.odd x]
  have hPe : Function.Even (fun x => ρ x*coercivePolynomial r x) := by
    intro x;dsimp only;rw [hρe x,coercivePolynomial_even hr.smooth hshape.odd x]
  have hfull : (1661507/1521000000:ℝ)*(∫ x, ρ x*quarticMoment r x) ≤ ∫ x, ρ x*coercivePolynomial r x := by
    rw [integral_even_two_Ioi hVe,integral_even_two_Ioi hPe]
    nlinarith only [hhalf]
  exact (mul_le_mul_of_nonneg_right Certificate.coercivity_constant.le
    (integral_nonneg (fun x => mul_nonneg (hρpos x) (by exact pow_nonneg (le_of_lt (hshape.derivative_pos x)) 4)))).trans hfull

end ZeroTemperatureSK.Heat

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
-- module Solutions.OAIQW_ZeroTemperatureSK.Diffusion.FiniteFeedback
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

lemma finiteValue_shift {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j ≤ N) (i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    finiteValue c h f N i ((j:ℝ)*h+t)=finiteValue c h f (N-j) (i+j) t := by
  induction j generalizing N i with
  | zero => simp
  | succ j ih =>
    cases N with
    | zero => omega
    | succ N =>
      have hh : (h:ℝ) ≤ ((j+1:ℕ):ℝ)*h+t := by push_cast;nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
      rw [finiteValue_tail_of_le hf hLip c h N i hh]
      have he : ((j+1:ℕ):ℝ)*(h:ℝ)+t-h=(j:ℝ)*h+t := by push_cast;ring
      rw [he,ih (by omega)]
      rw [show (N+1)-(j+1)=N-j by omega,show i+1+j=i+(j+1) by omega]

lemma rightCoeff_shift (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j ≤ N)
    (i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    rightCoeff c h N i ((j:ℝ)*h+t)=rightCoeff c h (N-j) (i+j) t := by
  induction j generalizing N i with
  | zero => simp
  | succ j ih =>
    cases N with
    | zero => omega
    | succ N =>
      have hh : ¬((j+1:ℕ):ℝ)*(h:ℝ)+t<h := by push_cast;nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) h.coe_nonneg]
      rw [rightCoeff,ite_eq_right hh]
      have he : ((j+1:ℕ):ℝ)*(h:ℝ)+t-h=(j:ℝ)*h+t := by push_cast;ring
      rw [he,ih (by omega)]
      rw [show (N+1)-(j+1)=N-j by omega,show i+1+j=i+(j+1) by omega]

lemma finiteFeedback_step {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N j : ℕ} (hj : j < N) {t : ℝ}
    (ht : t ∈ Ico ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h)) (x : ℝ) :
    (finiteFeedback hf hLip c h N 0).f t x =
      (c j:ℝ)*deriv (varianceLogHeat (c j) (((j+1:ℕ):ℝ)*h-t)
        (backwardBoundary c h f N (j+1))) x := by
  let τ := t-(j:ℝ)*h
  have hτ : 0 ≤ τ := sub_nonneg.mpr ht.1
  have hτh : τ < h := by dsimp [τ];have hh := ht.2;push_cast at hh;linarith
  have he : t=(j:ℝ)*h+τ := by dsimp [τ];ring
  change rightCoeff c h N 0 t*deriv (finiteValue c h f N 0 t) x=_
  rw [he,rightCoeff_shift c h hj.le 0 hτ,finiteValue_shift hf hLip c h hj.le 0 hτ]
  have hn : N-j=(N-(j+1))+1 := by omega
  simp only [Nat.zero_add,hn,rightCoeff,ite_eq_left hτh,finiteValue_head f c h (N-(j+1)) j hτh.le]
  have he' : (h:ℝ)-τ=((j+1:ℕ):ℝ)*h-((j:ℝ)*h+τ) := by push_cast;ring
  change (c j:ℝ)*deriv (varianceLogHeat (c j) ((h:ℝ)-τ) (cascade c h f (N-(j+1)) (j+1))) x=_
  rw [he']
  rfl

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

end ZeroTemperatureSK

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

lemma generator_add (F G : TimeField T) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.add G).generator b t x=F.generator b t x+G.generator b t x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hG (x : ℝ) := ((G.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hGd (x : ℝ) := ((G.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => F.f t y+G.f t y)=fun y => deriv (F.f t) y+deriv (G.f t) y :=
    funext (fun y => ((hF y).add (hG y)).deriv)
  dsimp only [generator,add]
  have hd := ((hFd x).add (hGd x)).deriv
  change deriv (fun y => deriv (F.f t) y+deriv (G.f t) y) x = _ at hd
  rw [he,hd]
  ring

lemma generator_const_mul (F : TimeField T) (c : ℝ) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (F.const_mul c).generator b t x=c*F.generator b t x := by
  have hF (x : ℝ) := ((F.smooth.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have hFd (x : ℝ) := ((F.smooth.deriv.regular t).smooth.differentiable (by simp) x).hasDerivAt
  have he : deriv (fun y => c*F.f t y)=fun y => c*deriv (F.f t) y :=
    funext (fun y => ((hF y).const_mul c).deriv)
  dsimp only [generator,const_mul]
  rw [he,((hFd x).const_mul c).deriv]
  ring

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
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

lemma finiteCoeff_offset (c d : ℕ → ℝ≥0) (h : ℝ≥0) (ε : ℝ) (N i : ℕ)
    (he : ∀ j < N, (d (i+j):ℝ)=(c (i+j):ℝ)+ε)
    {t : ℝ} (ht : t ≤ (N:ℝ)*h) (hN : 0 < N) :
    finiteCoeff d h N i t=finiteCoeff c h N i t+ε := by
  induction N generalizing i t with
  | zero => omega
  | succ N ih =>
    by_cases hh : t ≤ h
    · simp only [finiteCoeff,ite_eq_left hh]
      simpa only [Nat.add_zero] using he 0 (by omega)
    · simp only [finiteCoeff,ite_eq_right hh]
      have hp : 0 < N := by
        by_contra hn
        have hn0 : N=0 := by omega
        subst N
        norm_num at ht
        exact hh ht
      apply ih (i+1) _ _ hp
      · intro j hj
        simpa only [show i+1+j=i+(j+1) by omega] using he (j+1) (by omega)
      · push_cast at ht
        nlinarith

lemma positiveCoeff_pos (γ : OrderParameter) (n j : ℕ) : 0 < (positiveCoeff γ n j:ℝ) := by
  unfold positiveCoeff
  exact_mod_cast add_pos_of_nonneg_of_pos (bot_le : 0 ≤ approxCoeff γ n (min j n)) (approxMesh_pos n)

lemma positiveCoeff_monotone (γ : OrderParameter) (n : ℕ) : Monotone (positiveCoeff γ n) := by
  intro i j hij
  unfold positiveCoeff
  apply add_le_add _ le_rfl
  apply NNReal.coe_le_coe.mp
  rw [approxCoeff_eq γ n _ (by omega),approxCoeff_eq γ n _ (by omega)]
  apply γ.monotone
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_min_right n hij) (approxMesh n).coe_nonneg

lemma positiveCoeff_bound (γ : OrderParameter) (n j : ℕ) : (positiveCoeff γ n j:ℝ) ≤ positiveTerminal γ n := by
  have he : positiveCoeff γ n j=positiveCoeff γ n (min j n) := by simp only [positiveCoeff,min_assoc,min_self]
  have hh := positiveCoeff_monotone γ n (min_le_right j n)
  rw [← he] at hh
  unfold positiveTerminal
  exact (show (positiveCoeff γ n j:ℝ) ≤ positiveCoeff γ n n from hh).trans (by linarith [Nat.cast_nonneg (α := ℝ) (n+1)])

lemma positiveGamma_eq (γ : OrderParameter) (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    positiveGamma γ n t=approxGamma γ n t+(approxMesh n:ℝ) := by
  apply finiteCoeff_offset _ _ _ _ (n+1) 0 _ (by simpa only [approxMesh_horizon] using ht) (by omega)
  intro j hj
  simp only [Nat.zero_add,positiveCoeff,min_eq_left (by omega : j ≤ n),NNReal.coe_add]

lemma positiveGamma_intervalIntegrable (γ : OrderParameter) (n : ℕ) :
    IntervalIntegrable (positiveGamma γ n) volume 0 1 := finiteCoeff_intervalIntegrable _ _ _ _ _ _

lemma positiveGamma_L1_bound (γ : OrderParameter) (n : ℕ) :
    (∫ t in (0:ℝ)..1, |positiveGamma γ n t-extend γ.val t|) ≤
      (∫ t in (0:ℝ)..1, |approxGamma γ n t-extend γ.val t|)+(approxMesh n:ℝ) := by
  have hf : IntervalIntegrable (fun t => |approxGamma γ n t-extend γ.val t|) volume 0 1 := ((finiteCoeff_intervalIntegrable (approxCoeff γ n) (approxMesh n) (n+1) 0 0 1).sub γ.integrable.intervalIntegrable).abs
  have hg := ((positiveGamma_intervalIntegrable γ n).sub γ.integrable.intervalIntegrable).abs
  calc
    _ ≤ ∫ t in (0:ℝ)..1, |approxGamma γ n t-extend γ.val t|+(approxMesh n:ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hg (hf.add intervalIntegrable_const)
      intro t ht
      rw [positiveGamma_eq γ n ht.2]
      have he : approxGamma γ n t+(approxMesh n:ℝ)-extend γ.val t=
        (approxGamma γ n t-extend γ.val t)+(approxMesh n:ℝ) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (approxMesh n).coe_nonneg])
    _ = _ := by rw [intervalIntegral.integral_add hf intervalIntegrable_const,intervalIntegral.integral_const];simp

lemma positiveGamma_L1 (γ : OrderParameter) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1, |positiveGamma γ n t-extend γ.val t|) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _))
    (positiveGamma_L1_bound γ)
  simpa only [zero_add] using (approxGamma_L1 γ).add approxMesh_limit

lemma positiveGamma_bound (γ : OrderParameter) (n : ℕ) (t : Time) :
    positiveGamma γ n t ≤ γ.val t+1 := by
  rw [positiveGamma_eq γ n t.property.2.le]
  have hm : (approxMesh n:ℝ) ≤ 1 := by
    unfold approxMesh
    simp only [NNReal.coe_inv,NNReal.coe_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  exact add_le_add (approxGamma_bounds γ n t).2 hm

lemma positiveTerminal_inv_tendsto (γ : OrderParameter) :
    Tendsto (fun n => (positiveTerminal γ n)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => inv_nonneg.mpr (positiveTerminal_pos γ n).le) (fun n => ?_) approxMesh_limit
  change (positiveTerminal γ n)⁻¹ ≤ (((n+1:ℕ):ℝ))⁻¹
  apply inv_anti₀ (by positivity)
  unfold positiveTerminal
  exact le_add_of_nonneg_right (positiveCoeff γ n n).coe_nonneg

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Regularity.PositiveRegularity
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
open WeakIto Heat Nonuniform

lemma positiveError_limit (γ : OrderParameter) : Tendsto (positiveError γ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.log 2 / positiveTerminal γ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      tendsto_const_nhds.mul (positiveTerminal_inv_tendsto γ) (a := Real.log 2)
  have hi := tendsto_const_nhds.mul (positiveGamma_L1 γ) (a := (3/2:ℝ))
  have h := hh.add hi
  unfold positiveError
  convert h using 1 <;> try rfl
  simp only [mul_zero,add_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma positiveValue_error (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |positiveValue γ n t x-value W γ t x| ≤ positiveError γ n := by
  apply finiteValue_control_error W γ _ _ _ (approxMesh_horizon n)
    (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n))) (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ ht0 ht1 x
  intro z
  have hh := softAbs_bounds (positiveTerminal_pos γ n) z
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma positiveValue_uniform (W : BrownianSystem Ω) (γ : OrderParameter) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => positiveValue γ n p.1 p.2)
      (fun p => value W γ p.1 p.2) atTop (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(positiveError_limit γ).eventually (gt_mem_nhds hε)] with n hn p hp
  rw [Real.dist_eq,abs_sub_comm]
  exact (positiveValue_error W γ n hp.1.1 hp.1.2 p.2).trans_lt hn

lemma positiveValue_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformly (fun n => positiveValue γ n t) (value W γ t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(positiveError_limit γ).eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (positiveValue_error W γ n ht0 ht1 x).trans_lt hn

lemma positiveValue_regular (γ : OrderParameter) (n : ℕ) (t : ℝ) :
    RegularDatum (positiveValue γ n t) :=
  finiteValue_regular (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ _ _ _ _

lemma positiveValue_uniform_derivative_bounds (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (positiveValue γ n t) x| ≤ C := by
  let δ := (1-T)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : T+δ ∈ Ico (0:ℝ) 1 := by dsimp [δ]; constructor <;> linarith
  let D := γ.val ⟨T+δ,hB⟩+1
  obtain ⟨C,hC,hbound⟩ := finiteGradient_uniform_smoothing m D (by dsimp [D]; linarith [γ.nonneg ⟨T+δ,hB⟩]) δ hδ
  refine ⟨C,hC,fun n t ht x => ?_⟩
  have hc : ∀ s ∈ Icc (0:ℝ) (T+δ),
      finiteCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D := by
    intro s hs
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hs.1,hs.2.trans_lt hB.2⟩
    have hh := γ.monotone (show (⟨s,hmem⟩ : Time) ≤ ⟨T+δ,hB⟩ from hs.2)
    exact (positiveGamma_bound γ n ⟨s,hmem⟩).trans (add_le_add hh le_rfl)
  have hh := hbound _ (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) (positiveCoeff γ n) (approxMesh n) (n+1) 0 T hT0
    (by rw [approxMesh_horizon]; exact hB.2.le) hc m le_rfl t ht x
  simpa only [positiveValue,iteratedDeriv_succ'] using hh

lemma positiveValue_derivative_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (positiveValue γ n t))
      (iteratedDeriv m (value W γ t)) atTop := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (positiveValue_regular γ n t).smooth) _
    (positiveValue_uniform_spatial W γ ht0 ht1.le)).2 m
  intro j
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ ht0 ht1 (j+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

lemma positiveValue_derivative_uniform (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => iteratedDeriv m (positiveValue γ n p.1) p.2)
      (fun p => iteratedDeriv m (value W γ p.1) p.2) atTop (Icc (0:ℝ) T ×ˢ Set.univ) := by
  induction m with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (positiveValue_uniform W γ).mono (Set.prod_mono (Icc_subset_Icc le_rfl hT1.le) (Subset.refl _))
  | succ m ih =>
    obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ hT0 hT1 (m+1)
    have hbg : ∀ t ∈ Icc (0:ℝ) T, ∀ x, |iteratedDeriv (m+2) (value W γ t) x| ≤ C := by
      intro t ht x
      exact iteratedDeriv_limit_bound (m+2)
        (positiveValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+2))
        (fun n y => by simpa only [Nat.add_assoc] using hb n t ht y) x
    have hh := tendstoUniformlyOn_deriv_family (S := Icc (0:ℝ) T)
      (f := fun n t => iteratedDeriv m (positiveValue γ n t))
      (g := fun t => iteratedDeriv m (value W γ t))
      (fun n t _ => (contDiff_iteratedDeriv_infty (positiveValue_regular γ n t).smooth m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun t ht => (contDiff_iteratedDeriv_infty (value_contDiff W γ ht.1 (ht.2.trans_lt hT1)) m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hb)
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbg) ih
    simpa only [iteratedDeriv_succ] using hh

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.CoerciveMoments
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

lemma quarticMoment_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    quarticMoment (fun y => c*deriv f y) x=quarticJetPolynomial c (iteratedDeriv 2 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [quarticMoment,certV,he,quarticJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma coercivePolynomial_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    coercivePolynomial (fun y => c*deriv f y) x=coerciveJetPolynomial c
      (iteratedDeriv 2 f x) (iteratedDeriv 3 f x) (iteratedDeriv 4 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [coercivePolynomial,certV,certW,certZ,he,scaled_jet hd,
    coerciveJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma quarticJetPolynomial_bound {c A D E : ℝ} (hc : |c| ≤ D) (hA : |A| ≤ E) :
    |quarticJetPolynomial c A| ≤ D^4*E^4 := by
  simp only [quarticJetPolynomial,abs_mul,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 4) (pow_le_pow_left₀ (abs_nonneg _) hA 4)
    (by positivity) (by positivity)

lemma coerciveJetPolynomial_bound {c A B C D E F G : ℝ}
    (hc : |c| ≤ D) (hA : |A| ≤ E) (hB : |B| ≤ F) (hC : |C| ≤ G) :
    |coerciveJetPolynomial c A B C| ≤ D^2*G^2+12*D^3*E*F^2+6*D^4*E^4 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hc
  have hE : 0 ≤ E := (abs_nonneg _).trans hA
  have hF : 0 ≤ F := (abs_nonneg _).trans hB
  have hG : 0 ≤ G := (abs_nonneg _).trans hC
  have h1 : |c^2*C^2| ≤ D^2*G^2 := by
    simp only [abs_mul,abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 2) (pow_le_pow_left₀ (abs_nonneg _) hC 2) (by positivity) (by positivity)
  have h2 : |12*c^3*A*B^2| ≤ 12*D^3*E*F^2 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12)]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 3) (by norm_num)) hA (abs_nonneg _) (by positivity))
      (pow_le_pow_left₀ (abs_nonneg _) hB 2) (by positivity) (by positivity)
  have h3 : |6*c^4*A^4| ≤ 6*D^4*E^4 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 4) (by norm_num))
      (pow_le_pow_left₀ (abs_nonneg _) hA 4) (by positivity) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma sampleIndex_lt (n : ℕ) (t : Time) : sampleIndex n t < n+1 := by
  unfold sampleIndex
  rw [Nat.floor_lt (div_nonneg t.property.1 (approxMesh n).coe_nonneg),div_lt_iff₀ (by exact_mod_cast approxMesh_pos n),approxMesh_horizon]
  exact t.property.2

lemma sampleNNTime_lower (n : ℕ) (t : Time) : (t:ℝ)-(approxMesh n:ℝ) < sampleNNTime n t := by
  have hh := Nat.lt_floor_add_one ((t:ℝ)/(approxMesh n:ℝ))
  rw [div_lt_iff₀ (by exact_mod_cast approxMesh_pos n)] at hh
  change (t:ℝ)-(approxMesh n:ℝ) < (sampleIndex n t:ℝ)*(approxMesh n:ℝ)
  dsimp only [sampleIndex]
  nlinarith

lemma sampleTime_limit (t : Time) : Tendsto (fun n => sampleTime n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => (t:ℝ)-(approxMesh n:ℝ)) atTop (𝓝 (t:ℝ)) by
      simpa only [sub_zero] using tendsto_const_nhds.sub approxMesh_limit) tendsto_const_nhds
    (fun n => (sampleNNTime_lower n t).le) (fun n => sampleNNTime_le n t)

lemma sampleNNTime_limit (t : Time) : Tendsto (fun n => sampleNNTime n t) atTop (𝓝 (⟨t,t.property.1⟩:ℝ≥0)) := by
  apply tendsto_subtype_rng.mpr
  exact (continuous_subtype_val.tendsto t).comp (sampleTime_limit t)

lemma sampleIndex_pos_eventually (t : Time) (ht : 0 < (t:ℝ)) : ∀ᶠ n in atTop, 0 < sampleIndex n t := by
  filter_upwards [approxMesh_limit.eventually (gt_mem_nhds ht)] with n hn
  rw [sampleIndex,Nat.floor_pos,le_div_iff₀ (by exact_mod_cast approxMesh_pos n)]
  simpa only [one_mul] using hn.le

lemma positiveCoeff_sample_eq (γ : OrderParameter) (n : ℕ) (t : Time) :
    (positiveCoeff γ n (sampleIndex n t):ℝ)=γ.val (sampleTime n t)+(approxMesh n:ℝ) := by
  unfold positiveCoeff
  rw [min_eq_left (by have := sampleIndex_lt n t;omega),NNReal.coe_add,approxCoeff_eq γ n _ (sampleIndex_lt n t)]
  rfl

lemma positiveCoeff_sample_limit (γ : OrderParameter) (t : Time) (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => (positiveCoeff γ n (sampleIndex n t):ℝ)) atTop (𝓝 (γ.val t)) := by
  simp_rw [positiveCoeff_sample_eq]
  simpa only [add_zero,Function.comp_apply] using (ht.tendsto.comp (sampleTime_limit t)).add approxMesh_limit

lemma positiveCoeff_sample_bound (γ : OrderParameter) (n : ℕ) (t : Time) :
    (positiveCoeff γ n (sampleIndex n t):ℝ) ≤ γ.val t+1 := by
  rw [positiveCoeff_sample_eq]
  apply add_le_add (γ.monotone (sampleNNTime_le n t))
  unfold approxMesh
  simp only [NNReal.coe_inv,NNReal.coe_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

lemma positiveValue_sample (γ : OrderParameter) (n : ℕ) (t : Time) :
    positiveValue γ n (sampleTime n t)=backwardBoundary (positiveCoeff γ n) (approxMesh n)
      (softAbs (positiveTerminal γ n)) (n+1) (sampleIndex n t) := by
  have hf := regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n))
  have hLip := softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))
  have hh := finiteValue_shift hf hLip (positiveCoeff γ n) (approxMesh n)
    ((sampleIndex_lt n t).le) 0 (le_refl (0:ℝ))
  simp only [add_zero,Nat.zero_add,finiteValue_zero hf hLip] at hh
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

lemma heatKernel_complete_square {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x y : ℝ) :
    heatKernel t (y-x)*Real.exp (-y^2/(2*a)) =
      Real.sqrt (a/(a+t))*Real.exp (-x^2/(2*(a+t)))*
        heatKernel (a*t/(a+t)) (y-a/(a+t)*x) := by
  have hs := add_pos ha ht
  have hv : 0 < a*t/(a+t) := div_pos (mul_pos ha ht) hs
  have hscale : 0 < a/(a+t) := div_pos ha hs
  have he : -(y-x)^2/(2*t)+ -y^2/(2*a)=
      -x^2/(2*(a+t))+ -(y-a/(a+t)*x)^2/(2*(a*t/(a+t))) := by
    field_simp [ne_of_gt ha,ne_of_gt ht,ne_of_gt hs]
    ring
  have hroot : Real.sqrt (2*Real.pi*(a*t/(a+t))) =
      Real.sqrt (a/(a+t))*Real.sqrt (2*Real.pi*t) := by
    rw [← Real.sqrt_mul hscale.le]
    congr 1
    ring
  have hn : (Real.sqrt (2*Real.pi*t))⁻¹ =
      Real.sqrt (a/(a+t))*(Real.sqrt (2*Real.pi*(a*t/(a+t))))⁻¹ := by
    rw [hroot,mul_inv_rev]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hscale)]
  rw [heatKernel_formula ht.le,heatKernel_formula hv.le]
  rw [mul_assoc,← Real.exp_add,he,Real.exp_add,hn]
  ring

lemma varianceHeat_gaussian_weight {L : ℝ → ℝ} (hL : Measurable L)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    varianceHeat t (fun y => Real.exp (-y^2/(2*a)+L y)) x =
      Real.sqrt (a/(a+t))*Real.exp (-x^2/(2*(a+t)))*
        varianceHeat (a*t/(a+t)) (fun y => Real.exp (L y)) (a/(a+t)*x) := by
  have hm : Measurable (fun y : ℝ => Real.exp (-y^2/(2*a)+L y)) := by fun_prop
  rw [varianceHeat_kernel hm ht,varianceHeat_kernel hL.exp (div_pos (mul_pos ha ht) (add_pos ha ht))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Real.exp_add,← mul_assoc,heatKernel_complete_square ha ht]
  ring

lemma exp_varianceLogHeat_one {L : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K L) (t x : ℝ) :
    Real.exp (varianceLogHeat 1 t L x)=varianceHeat t (fun y => Real.exp (L y)) x := by
  simp only [varianceLogHeat,one_ne_zero,ite_false,div_one,one_mul]
  exact Real.exp_log (by simpa only [one_mul] using varianceHeat_exp_pos hL 1 t x)

lemma exp_half_log {x : ℝ} (hx : 0 < x) : Real.exp ((1/2:ℝ)*Real.log x)=Real.sqrt x := by
  apply (sq_eq_sq₀ (Real.exp_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hx.le,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((1/2)*Real.log x)=Real.log x by ring,Real.exp_log hx]

lemma varianceHeat_gaussian_forwardCorrection {L : ℝ → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K L) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    varianceHeat t (fun y => Real.exp (-y^2/(2*a)+L y)) x =
      Real.exp (-x^2/(2*(a+t))+forwardCorrection a L t x) := by
  rw [varianceHeat_gaussian_weight hL.continuous.measurable ha ht]
  simp only [forwardCorrection,forwardVariance,forwardScale,forwardTime,max_eq_left ht.le]
  rw [Real.exp_add,Real.exp_add,exp_varianceLogHeat_one hL,exp_half_log (div_pos ha (add_pos ha ht))]
  ring

end ZeroTemperatureSK.Heat

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

lemma BoundedLipschitzDrift.solution_zero (b : BoundedLipschitzDrift) (W : BrownianSystem Ω) (w : Ω) :
    b.solution W.driver 0 w=0 := by
  rw [b.solution_eq _ W.driver_progressive]
  simp only [W.driver_zero,NNReal.coe_zero,intervalIntegral.integral_same,add_zero]

lemma Heat.backwardBoundary_step {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    varianceLogHeat (c i) (h:ℝ) (backwardBoundary c h f N (i+1))=backwardBoundary c h f N i := by
  have hn : N-i=(N-(i+1))+1 := by omega
  funext x
  unfold backwardBoundary
  rw [varianceLogHeat_eq_logSemigroup_toNNReal (cascade_regular hf hLip c h _ _).smooth.continuous.measurable,
    Real.toNNReal_coe]
  simp only [hn,cascade]

lemma Heat.exp_varianceLogHeat {f : ℝ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K f)
    {c : ℝ} (hc : c ≠ 0) (t x : ℝ) :
    Real.exp (c*varianceLogHeat c t f x)=varianceHeat t (fun y => Real.exp (c*f y)) x := by
  simp only [varianceLogHeat,ite_eq_right hc]
  rw [mul_div_cancel₀ _ hc,Real.exp_log (varianceHeat_exp_pos hLip c t x)]

theorem finite_transition_tilted (W : BrownianSystem Ω) {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) {N i : ℕ} (hi : i < N) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i+1:ℕ)*h) w) ∂W.law)=
      ∫ w, varianceTilted (c i) h (backwardBoundary c h f N (i+1)) g
        ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h) w) ∂W.law := by
  have ht : (i:ℝ≥0)*h ≤ ((i+1:ℕ):ℝ≥0)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) h.coe_nonneg
  have hh := expected_transition_tiltedMean W (finiteFeedback hf hLip c h N 0)
    (cascade_regular hf hLip c h (N-(i+1)) (i+1)) (cascade_lipschitz hLip c h _ _) hg (c i).coe_nonneg ht
    (fun t htt x => by
      have he := finiteFeedback_step hf hLip c h hi (t := t) (by simpa only [NNReal.coe_mul,NNReal.coe_natCast] using htt) x
      simpa only [NNReal.coe_mul,NNReal.coe_natCast,backwardBoundary] using he)
  have he : ((((i+1:ℕ):ℝ≥0)*h:ℝ≥0):ℝ)-(((i:ℝ≥0)*h:ℝ≥0):ℝ)=(h:ℝ) := by push_cast;ring
  simpa only [he,backwardBoundary] using hh

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.DensityFubini
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

lemma heatKernel_even (t x : ℝ) : heatKernel t (-x)=heatKernel t x := by
  simp only [heatKernel,gaussianPDFReal,sub_zero,neg_sq]

lemma heatKernel_measurable (t : ℝ) : Measurable (heatKernel t) := measurable_gaussianPDFReal 0 _

lemma integrable_gaussian_heat_product {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ExponentialBound f) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-p.1^2/(2*a))*f p.1*heatKernel t (p.2-p.1)*g p.2)
      (volume.prod volume) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  let d := 1/(8*(a+t))
  have hd : 0 < d := by dsimp [d];positivity
  have hmajor := ((integrable_gaussian_linear hd K).mul_prod (integrable_gaussian_linear hd J)).const_mul
    ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)
  apply hmajor.mono'
  · exact ((((measurable_id.fst.pow_const 2).neg.div_const (2*a)).exp.mul (hfm.comp measurable_fst)).mul
      ((heatKernel_measurable t).comp (measurable_snd.sub measurable_fst)) |>.mul (hgm.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (heatKernel_pos ht _)]
    have he := gaussian_convolution_quadratic ha ht p.1 p.2
    change d*(p.1^2+p.2^2) ≤ _ at he
    have hk := (heatKernel_pos ht (p.2-p.1)).le
    calc
      Real.exp (-p.1^2/(2*a))*|f p.1| * heatKernel t (p.2-p.1)*|g p.2| ≤
          Real.exp (-p.1^2/(2*a))*((A:ℝ)*Real.exp ((K:ℝ)*|p.1|))*heatKernel t (p.2-p.1)*
            ((B:ℝ)*Real.exp ((J:ℝ)*|p.2|)) := by
        apply mul_le_mul _ (hB p.2) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hA p.1) (Real.exp_nonneg _)) hk
      _ = ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)*
          Real.exp (-p.1^2/(2*a)-(p.2-p.1)^2/(2*t)+(K:ℝ)*|p.1|+(J:ℝ)*|p.2|) := by
        rw [heatKernel_formula ht.le]
        simp only [sub_eq_add_neg,neg_div,Real.exp_add]
        ring
      _ ≤ ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)*
          Real.exp ((-d*p.1^2+(K:ℝ)*|p.1|)+(-d*p.2^2+(J:ℝ)*|p.2|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        simp only [neg_div]
        nlinarith only [he]
      _ = _ := by rw [Real.exp_add]

lemma gaussian_heat_pairing {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ExponentialBound f) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ x, (Real.exp (-x^2/(2*a))*f x)*varianceHeat t g x) =
      ∫ y, varianceHeat t (fun x => Real.exp (-x^2/(2*a))*f x) y*g y := by
  have hprod := integrable_gaussian_heat_product hfm hgm hf hg ha ht
  have hwm : Measurable (fun x : ℝ => Real.exp (-x^2/(2*a))*f x) := by fun_prop
  calc
    _ = ∫ x, ∫ y, Real.exp (-x^2/(2*a))*f x*heatKernel t (y-x)*g y := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [varianceHeat_kernel hgm ht,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y, ∫ x, Real.exp (-x^2/(2*a))*f x*heatKernel t (y-x)*g y :=
      integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [varianceHeat_kernel hwm ht,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show y-x=-(x-y) by ring,heatKernel_even]
      ring

lemma gaussian_heat_forward_pairing {L g : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K L)
    (hgm : Measurable g) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ x, Real.exp (-x^2/(2*a)+L x)*varianceHeat t g x) =
      ∫ y, Real.exp (-y^2/(2*(a+t))+forwardCorrection a L t y)*g y := by
  have hf := exponentialBound_exp hL 1
  simp only [one_mul] at hf
  have hh := gaussian_heat_pairing hL.continuous.measurable.exp hgm hf hg ha ht
  have he : (fun x : ℝ => Real.exp (-x^2/(2*a))*Real.exp (L x))=
      fun x => Real.exp (-x^2/(2*a)+L x) := by funext x;rw [Real.exp_add]
  simp_rw [he,varianceHeat_gaussian_forwardCorrection hL ha ht] at hh
  simpa only [Real.exp_add] using hh

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma density_tilted_pairing {L f g : ℝ → ℝ} {K J : ℝ≥0}
    (hL : LipschitzWith K L) (hf : LipschitzWith J f) (hg : BoundedSmooth g)
    {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : c ≠ 0) :
    (∫ x, Real.exp (c*varianceLogHeat c t f x-x^2/(2*a)+L x)*varianceTilted c t f g x)=
      ∫ y, Real.exp (c*f y-y^2/(2*(a+t))+forwardCorrection a L t y)*g y := by
  obtain ⟨G,hG⟩ := hg.bound
  have hwm : Measurable (fun y => g y*Real.exp (c*f y)) := by
    exact hg.smooth.continuous.measurable.mul ((measurable_const.mul hf.continuous.measurable).exp)
  have hw := (exponentialBound_exp hf c).bdd_mul hG
  calc
    _ = ∫ x, Real.exp (-x^2/(2*a)+L x)*varianceHeat t (fun y => g y*Real.exp (c*f y)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show c*varianceLogHeat c t f x-x^2/(2*a)+L x=
        (-x^2/(2*a)+L x)+c*varianceLogHeat c t f x by ring]
      rw [Real.exp_add,exp_varianceLogHeat hf hc]
      unfold varianceTilted
      field_simp [ne_of_gt (varianceHeat_exp_pos hf c t x)]
    _ = ∫ y, Real.exp (-y^2/(2*(a+t))+forwardCorrection a L t y)*
        (g y*Real.exp (c*f y)) := gaussian_heat_forward_pairing hL hwm hw ha ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [sub_eq_add_neg,neg_div,Real.exp_add]
      ring

lemma finiteDensity_step_pairing {f g : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hg : BoundedSmooth g) (c : ℕ → ℝ≥0) (hc : ∀ i, 0 < (c i:ℝ))
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i < N) :
    (∫ x, finiteDensity c h f N i x*varianceTilted (c i) h (backwardBoundary c h f N (i+1)) g x)=
      ∫ y, finiteDensity c h f N (i+1) y*g y := by
  obtain ⟨K,hK⟩ := (forwardBoundary_regular hf hLip c hh N i).exists_lipschitz
  have he := density_tilted_pairing hK (cascade_lipschitz hLip c h (N-(i+1)) (i+1)) hg
    (mul_pos (Nat.cast_pos.mpr hi) hh) hh (ne_of_gt (hc i))
  change (∫ x, Real.exp ((c i:ℝ)*varianceLogHeat (c i) h (backwardBoundary c h f N (i+1)) x-
    x^2/(2*((i:ℝ)*h))+forwardBoundary c h f N i x)*_) = _ at he
  rw [backwardBoundary_step hf hLip c h hiN] at he
  change (∫ x, finiteDensity c h f N i x*_) = _ at he
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  unfold finiteDensity
  rw [forwardBoundary]
  dsimp only
  rw [ite_eq_right (Nat.ne_of_gt hi)]
  congr 1
  simp only [backwardBoundary,Nat.cast_add,Nat.cast_one]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.FiniteDensity
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

lemma Heat.finiteDensity_first_formula (c : ℕ → ℝ≥0) {h : ℝ≥0}
    (hh : 0 < (h:ℝ)) (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    finiteDensity c h f N 1 x=heatKernel h x*
      Real.exp ((c 0:ℝ)*backwardBoundary c h f N 1 x-(c 0:ℝ)*backwardBoundary c h f N 0 0) := by
  have hn : Real.exp (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ)))=
      (Real.sqrt (2*Real.pi*(h:ℝ)))⁻¹ := by
    rw [show -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))= -((1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))) by ring,
      Real.exp_neg,exp_half_log (by positivity)]
  unfold finiteDensity
  rw [forwardBoundary]
  simp only [Nat.cast_one,one_mul,ite_true,Nat.zero_add]
  rw [show (c 1:ℝ)*backwardBoundary c h f N 1 x-x^2/(2*(h:ℝ))+
      (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-(c 0:ℝ)*backwardBoundary c h f N 0 0-
      ((c 1:ℝ)-(c 0:ℝ))*backwardBoundary c h f N 1 x)=
      (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ)))+(-x^2/(2*(h:ℝ)))+
      ((c 0:ℝ)*backwardBoundary c h f N 1 x-(c 0:ℝ)*backwardBoundary c h f N 0 0) by ring,
    Real.exp_add,Real.exp_add,hn,heatKernel_formula hh.le]

lemma Heat.finiteDensity_first_pairing {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (hc : 0 < (c 0:ℝ)) {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N : ℕ} (hN : 0 < N) :
    varianceTilted (c 0) h (backwardBoundary c h f N 1) g 0=
      ∫ x, finiteDensity c h f N 1 x*g x := by
  have hφ : LipschitzWith 1 (backwardBoundary c h f N 1) := cascade_lipschitz hLip c h _ _
  have hem := exp_varianceLogHeat hφ (ne_of_gt hc) (h:ℝ) 0
  rw [backwardBoundary_step hf hLip c h hN] at hem
  have hgm : Measurable (fun z => g z*Real.exp ((c 0:ℝ)*backwardBoundary c h f N 1 z)) :=
    hg.smooth.continuous.measurable.mul ((measurable_const.mul hφ.continuous.measurable).exp)
  unfold varianceTilted
  rw [← hem,varianceHeat_kernel hgm hh,← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [finiteDensity_first_formula c hh,Real.exp_sub]
  simp only [sub_zero]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_density_identity (W : BrownianSystem Ω) {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (hc : ∀ i, 0 < (c i:ℝ)) {h : ℝ≥0} (hh : 0 < (h:ℝ))
    {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h) w) ∂W.law)=
      ∫ x, finiteDensity c h f N i x*g x := by
  let := W.isProbability
  induction i generalizing g with
  | zero => omega
  | succ i ih =>
    rw [finite_transition_tilted W hf hLip hg c h (by omega : i < N)]
    by_cases h0 : i=0
    · subst i
      simp only [Nat.cast_zero,zero_mul,BoundedLipschitzDrift.solution_zero]
      simpa using finiteDensity_first_pairing hf hLip hg c (hc 0) hh (N := N) (by omega)
    · have hip : 0 < i := Nat.pos_of_ne_zero h0
      have hφ : RegularDatum (backwardBoundary c h f N (i+1)) := cascade_regular hf hLip c h _ _
      have hφL : LipschitzWith 1 (backwardBoundary c h f N (i+1)) := cascade_lipschitz hLip c h _ _
      have hgt := (varianceTilted_family hφ hφL hg (hc i).le).regular (h:ℝ)
      rw [ih hgt hip (by omega)]
      exact finiteDensity_step_pairing hf hLip hg c hc hh hip (by omega)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma datumScore_regular {L : ℝ → ℝ} (hL : RegularDatum L) (a : ℝ) : RegularDatum (datumScore a L) := by
  refine ⟨(contDiff_id.div_const a).sub (contDiff_infty_iff_deriv.mp hL.smooth |>.2),?_⟩
  have he : deriv (datumScore a L)=fun x => 1/a+(-1)*deriv (deriv L) x := by
    funext x
    rw [datumScore_deriv hL.smooth]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  rw [he]
  exact (BoundedSmooth.const _).add (hL.deriv_bounded.deriv.const_mul (-1))

lemma datumScore_odd {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (he : Function.Even L) (a : ℝ) :
    Function.Odd (datumScore a L) := by
  have hh := even_deriv_odd (hL.differentiable (by simp)) he
  intro x
  dsimp only [datumScore]
  rw [hh x]
  ring

lemma datumScore_second {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (a x : ℝ) :
    iteratedDeriv 2 (datumScore a L) x= -iteratedDeriv 3 L x := by
  have he : deriv (datumScore a L)=fun y => 1/a-iteratedDeriv 2 L y := by
    funext y;exact datumScore_deriv hL a y
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  rw [he]
  convert ((hasDerivAt_const x (1/a)).sub (hasDerivAt_spatialJet hL 2 x)).deriv using 1 <;> try rfl
  first | rfl | simp [iteratedDeriv_succ,iteratedDeriv_zero]

theorem finite_density_coercivity {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    let r := fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x
    (1/1000:ℝ)*(∫ x, finiteDensity c h (softAbs M) N i x*quarticMoment r x) ≤
      ∫ x, finiteDensity c h (softAbs M) N i x*coercivePolynomial r x := by
  let φ := backwardBoundary c h (softAbs M) N i
  let L := forwardBoundary c h (softAbs M) N i
  let a : ℝ := (i:ℝ)*h
  let r := fun x => (c i:ℝ)*deriv φ x
  let s := datumScore a L
  let U := fun x => (c i:ℝ)*φ x+L x
  let d : ℝ := 1/(2*a)
  have ha : 0 < a := mul_pos (Nat.cast_pos.mpr hi) hh
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  have hφ : RegularDatum φ := cascade_regular hf hLip c h _ _
  have hL : RegularDatum L := forwardBoundary_regular hf hLip c hh N i
  have hLe : ForwardDatumShape L := forwardBoundary_shape c hc hmono hM hh N i
  have hr : BoundedSmooth r := hφ.deriv_bounded.const_mul _
  have hs : RegularDatum s := datumScore_regular hL a
  have hshape : BackwardShape r := backwardBoundary_shape c hc hmono hM h N i
  have hso : Function.Odd s := datumScore_odd hL.smooth hLe.even a
  have hsa (x : ℝ) : 0 ≤ deriv s x := by
    rw [datumScore_deriv hL.smooth]
    linarith [hLe.second x,one_div_pos.mpr ha]
  have hsw (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 2 s x ≤ 0 := by
    rw [datumScore_second hL.smooth]
    exact neg_nonpos.mpr (hLe.third x hx)
  have hQ (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x*deriv s x-s x*deriv r x :=
    boundaryRatio_nonneg c hc hmono hM hh N i hi hiN x hx
  have hUr : RegularDatum U := by
    convert hL.sub_mul hφ (-(c i:ℝ)) using 1 <;> try rfl
    funext x;dsimp only [U];ring
  obtain ⟨K,hU⟩ := hUr.exists_lipschitz
  have hUe : Function.Even U := by
    have heφ : Function.Even φ := cascade_even hf hLip (softAbs_even M) c h _ _
    intro x
    dsimp only [U]
    rw [heφ x,hLe.even x]
  have hUd (x : ℝ) : HasDerivAt U (r x-s x+2*d*x) x := by
    have he : r x-s x+2*d*x=(c i:ℝ)*deriv φ x+deriv L x := by
      dsimp only [r,s,datumScore,d]
      field_simp [ne_of_gt ha]
      ring
    rw [he]
    convert (((hφ.smooth.differentiable (by simp)) x).hasDerivAt.const_mul (c i:ℝ)).add
      (((hL.smooth.differentiable (by simp)) x).hasDerivAt) using 1 <;> try rfl
  have he : finiteDensity c h (softAbs M) N i=gaussianLogDensity d U := by
    funext x
    unfold finiteDensity gaussianLogDensity
    congr 1
    dsimp only [d,U,a,φ,L]
    ring
  rw [he]
  exact gaussian_shape_coercivity hr hs hshape hso hsa hsw hQ hU hUe (by dsimp [d];positivity) hUd

end Heat
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_feedback_coercivity (W : BrownianSystem Ω) {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    let hMp : M ≠ 0 := ne_of_gt ((hc 0).trans_le (hM 0))
    let X := (finiteFeedback (regularDatum_softAbs hMp) (softAbs_lipschitz hMp) c h N 0).solution W.driver
    let r := fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x
    (1/1000:ℝ)*(∫ w, quarticMoment r (X ((i:ℝ≥0)*h) w) ∂W.law) ≤
      ∫ w, coercivePolynomial r (X ((i:ℝ≥0)*h) w) ∂W.law := by
  dsimp only
  have hMp : M ≠ 0 := ne_of_gt ((hc 0).trans_le (hM 0))
  have hr : BoundedSmooth (fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x) := (cascade_regular (regularDatum_softAbs hMp) (softAbs_lipschitz hMp) c h (N-i) i).deriv_bounded.const_mul (c i:ℝ)
  rw [finite_density_identity W (regularDatum_softAbs hMp) (softAbs_lipschitz hMp)
    (quarticMoment_boundedSmooth hr) c hc hh hi hiN,
    finite_density_identity W (regularDatum_softAbs hMp) (softAbs_lipschitz hMp)
    (coercivePolynomial_boundedSmooth hr) c hc hh hi hiN]
  exact finite_density_coercivity c hc hmono hM hh hi hiN

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.RightCoeffApprox
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

lemma rightCoeff_eq_finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (hne : ∀ k < N, t ≠ ((k+1:ℕ):ℝ)*h) : rightCoeff c h N i t=finiteCoeff c h N i t := by
  induction N generalizing i t with
  | zero => rfl
  | succ N ih =>
    have hh : t ≠ (h:ℝ) := by simpa using hne 0 (by omega)
    rw [rightCoeff,finiteCoeff]
    by_cases ht : t < h
    · rw [ite_eq_left ht,ite_eq_left ht.le]
    · rw [ite_eq_right ht,ite_eq_right (by exact not_le.mpr (lt_of_le_of_ne (le_of_not_gt ht) hh.symm))]
      apply ih
      intro k hk he
      apply hne (k+1) (by omega)
      have he' := he
      push_cast at he' ⊢
      linarith

lemma rightCoeff_ae (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    rightCoeff c h N i =ᵐ[volume] finiteCoeff c h N i := by
  have hn : ∀ᵐ t : ℝ, ∀ k : ℕ, t ≠ ((k+1:ℕ):ℝ)*h := by
    rw [ae_all_iff]
    intro k
    exact ae_iff.mpr (by simp)
  filter_upwards [hn] with t ht
  exact rightCoeff_eq_finiteCoeff c h N i (fun k _ => ht k)

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

lemma stripA_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Continuous (stripA W γ T) := by
  have hu := (compactGradient_family W γ T.property.1 T.property.2).deriv
  have hf : BoundedSmoothFamily (fun t x => (deriv (compactGradient W γ T t) x)^2) := by
    simpa only [pow_two] using hu.mul hu
  exact (stripDrift W γ T).expected_continuous W hf
    (compactCurvatureSquare_continuous W γ T.property.1 T.property.2)

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

lemma positiveCoeffError_limit (γ : OrderParameter) : Tendsto (positiveCoeffError γ) atTop (𝓝 0) := positiveGamma_L1 γ

lemma mul_sub_mul_error {a b u v D δ : ℝ} (hδ : 0 ≤ δ) (hD : |a| ≤ D)
    (hv : |v| ≤ 1) (huv : |u-v| ≤ δ) : |a*u-b*v| ≤ |a-b|+D*δ := by
  calc
    _ = |(a-b)*v+a*(u-v)| := by congr 1;ring
    _ ≤ |(a-b)*v|+|a*(u-v)| := abs_add_le _ _
    _ = |a-b| * |v|+|a| * |u-v| := by rw [abs_mul,abs_mul]
    _ ≤ |a-b| * 1+D*δ := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
      ((mul_le_mul_of_nonneg_left huv (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hD hδ))
    _ = _ := by ring

lemma positiveDrift_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s ∈ Icc (0:ℝ) T, ∀ x, |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ δ) :
    ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x,
      |(stripDrift W γ T).f s x-(positiveDrift γ n).f s x| ≤
        |positiveGamma γ n s-extend γ.val s|+γ.val T*δ := by
  filter_upwards [rightCoeff_ae (positiveCoeff γ n) (approxMesh n) (n+1) 0] with s hs hst x
  rw [stripDrift_eq W γ T hst]
  change |extend γ.val s*gradient W γ s x-rightCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0 s*
    deriv (positiveValue γ n s) x| ≤ _
  rw [hs]
  have ha : |extend γ.val s| ≤ γ.val T := by
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hst.1,hst.2.trans_lt T.property.2⟩
    simp only [extend,dite_eq_left hmem,abs_of_nonneg (γ.nonneg _)]
    exact γ.monotone hst.2
  have hu : |deriv (positiveValue γ n s) x| ≤ 1 := by
    exact norm_deriv_le_of_lipschitz (finiteValue_lipschitz
      (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ _ _ _ _) (x₀ := x)
  simpa only [positiveGamma,abs_sub_comm] using mul_sub_mul_error (b := positiveGamma γ n s) hδ ha hu (by simpa only [abs_sub_comm] using hd s hst x)

lemma positivePath_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s ∈ Icc (0:ℝ) T, ∀ x, |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ δ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |positivePath W γ n t ξ-diffusion W γ t ξ| ≤
      2*(positiveCoeffError γ n+γ.val T*(T:ℝ)*δ)*Real.exp ((stripDrift W γ T).rate*T) := by
  let e := fun s => |positiveGamma γ n s-extend γ.val s|+γ.val T*δ
  have hei (a b : ℝ) : IntervalIntegrable e volume a b :=
    (((finiteCoeff_intervalIntegrable (positiveCoeff γ n) (approxMesh n) (n+1) 0 a b).sub
      γ.integrable.intervalIntegrable).abs).add intervalIntegrable_const
  have hen (s : ℝ) : 0 ≤ e s := add_nonneg (abs_nonneg _) (mul_nonneg (γ.nonneg T) hδ)
  let TT : ℝ≥0 := ⟨T,T.property.1⟩
  have hh := (stripDrift W γ T).solution_stability_integral (positiveDrift γ n) _ W.driver_progressive TT
    (hei 0 T) (fun s _ => hen s) (positiveDrift_error W γ T n hδ hd) t ht ξ
  rw [← diffusion_eq_strip W γ T t ht] at hh
  rw [abs_sub_comm] at hh
  change |positivePath W γ n t ξ-diffusion W γ t ξ| ≤ _ at hh
  have hi0 : 0 ≤ ∫ s in (0:ℝ)..(T:ℝ), e s :=
    intervalIntegral.integral_nonneg T.property.1 (fun s _ => hen s)
  have hi : (∫ s in (0:ℝ)..(T:ℝ), e s) ≤ positiveCoeffError γ n+γ.val T*(T:ℝ)*δ := by
    have hgi (a b : ℝ) := ((finiteCoeff_intervalIntegrable (positiveCoeff γ n) (approxMesh n) (n+1) 0 a b).sub γ.integrable.intervalIntegrable).abs
    dsimp only [e,positiveGamma]
    rw [intervalIntegral.integral_add (hgi 0 T) intervalIntegrable_const,intervalIntegral.integral_const]
    dsimp only [positiveCoeffError]
    have hi := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := (T:ℝ))
      (c := (0:ℝ)) (d := 1) le_rfl T.property.1 T.property.2.le
      (Eventually.of_forall (fun s => abs_nonneg (positiveGamma γ n s-extend γ.val s))) (hgi 0 1)
    dsimp only [e,positiveGamma] at *
    simp only [sub_zero,smul_eq_mul] at *
    nlinarith only [hi]
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
-- module Solutions.OAIQW_ZeroTemperatureSK.Moments.PositiveGradientError
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

lemma positiveGradientErrors_bddAbove (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) :
    BddAbove (positiveGradientErrors W γ T n) := by
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ T.property.1 T.property.2 0
  refine ⟨C+1,?_⟩
  rintro z ⟨p,rfl⟩
  have hh := hb n (stripClamp T p.1) (stripClamp_mem T.property.1 p.1) p.2
  simp only [Nat.zero_add,iteratedDeriv_one] at hh
  exact (abs_sub _ _).trans (add_le_add hh (compactGradient_bound W γ T.property.1 T.property.2 p.1 p.2))

lemma positiveGradientError_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ) :
    0 ≤ positiveGradientError W γ T n := by
  exact (abs_nonneg _).trans (le_csSup (positiveGradientErrors_bddAbove W γ T n) ⟨((0:ℝ),(0:ℝ)),rfl⟩)

lemma positiveGradientError_bound (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (n : ℕ)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) T) (x : ℝ) :
    |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ positiveGradientError W γ T n := by
  have hh := le_csSup (positiveGradientErrors_bddAbove W γ T n)
    (show |deriv (positiveValue γ n (stripClamp T s)) x-compactGradient W γ T s x| ∈
      positiveGradientErrors W γ T n from ⟨(s,x),rfl⟩)
  simpa only [compactGradient,stripClamp_eq hs,positiveGradientError] using hh

lemma positiveGradientError_limit (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    Tendsto (positiveGradientError W γ T) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := positiveValue_derivative_uniform W γ T.property.1 T.property.2 1
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu (ε/2) (by linarith)] with n hn
  have he : positiveGradientError W γ T n ≤ ε/2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨p,rfl⟩
    have hh := hn (stripClamp T p.1,p.2) ⟨stripClamp_mem T.property.1 p.1,mem_univ _⟩
    simpa only [iteratedDeriv_one,Real.dist_eq,compactGradient,gradient,abs_sub_comm] using hh.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (positiveGradientError_nonneg W γ T n)]
  linarith

lemma positivePath_uniform_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t:ℝ) ≤ T → ∀ ξ,
      |positivePath W γ n t ξ-diffusion W γ t ξ| < ε := by
  let E (n : ℕ) := 2*(positiveCoeffError γ n+γ.val T*(T:ℝ)*positiveGradientError W γ T n)*
    Real.exp ((stripDrift W γ T).rate*T)
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh := (positiveCoeffError_limit γ).add
      (tendsto_const_nhds.mul (positiveGradientError_limit W γ T) (a := γ.val T*(T:ℝ)))
    simpa only [E,mul_zero,zero_add,zero_mul] using
      (tendsto_const_nhds.mul hh (a := (2:ℝ))).mul_const (Real.exp ((stripDrift W γ T).rate*T))
  intro ε hε
  filter_upwards [hE.eventually (gt_mem_nhds hε)] with n hn t ht ξ
  exact (positivePath_error W γ T n (positiveGradientError_nonneg W γ T n)
    (fun s hs x => positiveGradientError_bound W γ T n hs x) t ht ξ).trans_lt hn

end ZeroTemperatureSK

end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Density.SampleJets
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

lemma positivePath_sample_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) :
    ∀ᵐ ξ ∂W.law, Tendsto (fun n => positivePath W γ n (sampleNNTime n t) ξ) atTop
      (𝓝 (diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) := by
  filter_upwards [diffusion_continuous W γ] with ξ hc
  have hh := (hc.tendsto (⟨t,t.property.1⟩:ℝ≥0)).comp (sampleNNTime_limit t)
  rw [Metric.tendsto_nhds] at hh ⊢
  intro ε hε
  filter_upwards [positivePath_uniform_error W γ t (ε/2) (by linarith),hh (ε/2) (by linarith)] with n hn hξ
  have h := hn (sampleNNTime n t) (sampleNNTime_le n t) ξ
  apply lt_of_le_of_lt (dist_triangle _ (diffusion W γ (sampleNNTime n t) ξ) _)
  simp only [Real.dist_eq,Function.comp_apply] at *
  linarith

lemma sampleJet_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) :
    ∀ᵐ ξ ∂W.law, Tendsto (fun n => sampleJet W γ n t m ξ) atTop (𝓝 (actualJet W γ t m ξ)) := by
  filter_upwards [positivePath_sample_limit W γ t] with ξ hξ
  have hp : Tendsto (fun n => ((sampleTime n t:ℝ),positivePath W γ n (sampleNNTime n t) ξ)) atTop
      (𝓝 ((t:ℝ),diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) :=
    (((continuous_subtype_val.tendsto t).comp (sampleTime_limit t))).prodMk_nhds hξ
  have hpw : Tendsto (fun n => ((sampleTime n t:ℝ),positivePath W γ n (sampleNNTime n t) ξ)) atTop
      (𝓝[Icc (0:ℝ) t ×ˢ Set.univ] ((t:ℝ),diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hp,Eventually.of_forall (fun n => ?_)⟩
    exact ⟨⟨(sampleTime n t).property.1,sampleNNTime_le n t⟩,mem_univ _⟩
  exact (positiveValue_derivative_uniform W γ t.property.1 t.property.2 m).tendsto_comp
    (value_derivative_continuousOn W γ t.property.1 t.property.2 m _ ⟨⟨t.property.1,le_rfl⟩,mem_univ _⟩) hpw

lemma sampleJet_measurable (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) (t : Time) (m : ℕ) :
    Measurable (sampleJet W γ n t m) := by
  exact (contDiff_iteratedDeriv_infty (positiveValue_regular γ n (sampleTime n t)).smooth m).continuous.measurable.comp
    ((positiveDrift γ n).solution_measurable W (sampleNNTime n t))

lemma sampleJet_bound (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ξ, |sampleJet W γ n t (m+1) ξ| ≤ C := by
  obtain ⟨C,hC,hb⟩ := positiveValue_uniform_derivative_bounds γ t.property.1 t.property.2 m
  exact ⟨C,hC,fun n ξ => hb n (sampleTime n t) ⟨(sampleTime n t).property.1,sampleNNTime_le n t⟩ _⟩

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma sample_coercivity (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time) (n : ℕ)
    (hi : 0 < sampleIndex n t) :
    (1/1000:ℝ)*(∫ ξ, sampleQuartic W γ n t ξ ∂W.law) ≤ ∫ ξ, sampleCoercive W γ n t ξ ∂W.law := by
  have hs := (positiveValue_regular γ n (sampleTime n t)).smooth
  rw [positiveValue_sample] at hs
  have hh := finite_feedback_coercivity W (positiveCoeff γ n) (positiveCoeff_pos γ n)
    (positiveCoeff_monotone γ n) (positiveCoeff_bound γ n)
    (by exact_mod_cast approxMesh_pos n) hi ((sampleIndex_lt n t).le)
  dsimp only at hh
  simp_rw [quarticMoment_scaled hs,coercivePolynomial_scaled hs,← positiveValue_sample γ n t] at hh
  exact hh

lemma sampleQuartic_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => ∫ ξ, sampleQuartic W γ n t ξ ∂W.law) atTop
      (𝓝 (∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC,hb⟩ := sampleJet_bound W γ t 1
  have hm (n : ℕ) : AEStronglyMeasurable (sampleQuartic W γ n t) W.law := by
    have hh := sampleJet_measurable W γ n t 2
    exact (measurable_const.mul (hh.pow_const 4)).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (γ.val t+1)^4*C^4) hm
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun ξ => quarticJetPolynomial_bound
      (by rw [abs_of_nonneg (positiveCoeff γ n (sampleIndex n t)).coe_nonneg];exact positiveCoeff_sample_bound γ n t)
      (hb n ξ))
  · filter_upwards [sampleJet_limit W γ t 2] with ξ hξ
    exact ((positiveCoeff_sample_limit γ t ht).pow 4).mul (hξ.pow 4)

lemma sampleCoercive_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => ∫ ξ, sampleCoercive W γ n t ξ ∂W.law) atTop
      (𝓝 (∫ ξ, coerciveJetPolynomial (γ.val t)
        (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨A,hA,hbA⟩ := sampleJet_bound W γ t 1
  obtain ⟨B,hB,hbB⟩ := sampleJet_bound W γ t 2
  obtain ⟨C,hC,hbC⟩ := sampleJet_bound W γ t 3
  let D := γ.val t+1
  have hm (n : ℕ) : AEStronglyMeasurable (sampleCoercive W γ n t) W.law := by
    have h2 := sampleJet_measurable W γ n t 2
    have h3 := sampleJet_measurable W γ n t 3
    have h4 := sampleJet_measurable W γ n t 4
    exact (((measurable_const.mul (h4.pow_const 2)).sub ((measurable_const.mul h2).mul (h3.pow_const 2))).add
      (measurable_const.mul (h2.pow_const 4))).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => D^2*C^2+12*D^3*A*B^2+6*D^4*A^4) hm
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun ξ => coerciveJetPolynomial_bound
      (by rw [abs_of_nonneg (positiveCoeff γ n (sampleIndex n t)).coe_nonneg];exact positiveCoeff_sample_bound γ n t)
      (hbA n ξ) (hbB n ξ) (hbC n ξ))
  · filter_upwards [sampleJet_limit W γ t 2,sampleJet_limit W γ t 3,sampleJet_limit W γ t 4] with ξ h2 h3 h4
    have hc := positiveCoeff_sample_limit γ t ht
    exact (((hc.pow 2).mul (h4.pow 2)).sub (((hc.pow 3).const_mul 12).mul h2 |>.mul (h3.pow 2))).add
      (((hc.pow 4).const_mul 6).mul (h2.pow 4))

theorem actual_coercivity (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht0 : 0 < (t:ℝ)) (ht : ContinuousAt γ.val t) :
    (1/1000:ℝ)*(∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law) ≤
      ∫ ξ, coerciveJetPolynomial (γ.val t)
        (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law := by
  apply le_of_tendsto_of_tendsto ((sampleQuartic_integral_limit W γ t ht).const_mul (1/1000:ℝ))
    (sampleCoercive_integral_limit W γ t ht)
  filter_upwards [sampleIndex_pos_eventually t ht0] with n hn
  exact sample_coercivity W γ t n hn

end ZeroTemperatureSK

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

lemma compactRate_jet_three (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    iteratedDeriv 3 (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 4 t x-
      compactCoeff γ T t*(3*compactJet W γ T 1 t x*compactJet W γ T 2 t x+
        compactJet W γ T 0 t x*compactJet W γ T 3 t x) := by
  have he : iteratedDeriv 2 (compactValueRate W γ T t)=fun y => -(1/2:ℝ)*compactJet W γ T 3 t y-
      compactCoeff γ T t*((compactJet W γ T 1 t y)^2+compactJet W γ T 0 t y*compactJet W γ T 2 t y) :=
    funext (compactRate_jet_two W γ hT0 hT1 t)
  have hd (n : ℕ) := compactJet_hasDerivAt W γ hT0 hT1 n t x
  have hh := ((hd 3).const_mul (-(1/2:ℝ))).sub
    ((((hd 1).pow 2).add ((hd 0).mul (hd 2))).const_mul (compactCoeff γ T t))
  have hdv := hh.deriv
  change deriv (fun y => -(1/2:ℝ)*compactJet W γ T 3 t y-
      compactCoeff γ T t*((compactJet W γ T 1 t y)^2+compactJet W γ T 0 t y*compactJet W γ T 2 t y)) x = _ at hdv
  rw [show (3:ℕ)=2+1 from rfl,iteratedDeriv_succ,he,hdv]
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

lemma compactJetField_generator_two (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (compactJetField W γ hT0 hT1 2).generator (compactDrift W γ T) t x=
      -3*compactCoeff γ T t*compactJet W γ T 1 t x*compactJet W γ T 2 t x := by
  dsimp only [TimeField.generator,compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1,
    compactRate_jet_three W γ hT0 hT1]
  change compactJet W γ T 3 t x*(compactCoeff γ T t*compactJet W γ T 0 t x)+_+_= _
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

lemma curvatureField_deriv (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv ((curvatureField W γ hT0 hT1).f t) x=
      2*compactJet W γ T 1 t x*compactJet W γ T 2 t x := by
  have hd := compactJet_hasDerivAt W γ hT0 hT1 1 t x
  exact (hd.mul hd).deriv.trans (by ring)

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

lemma secondCurvatureField_generator (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) (hc : compactCoeff γ T t=c) :
    (secondCurvatureField W γ hT0 hT1 c).generator (compactDrift W γ T) t x=
      (compactJet W γ T 3 t x)^2-12*c*compactJet W γ T 1 t x*(compactJet W γ T 2 t x)^2+
        6*c^2*(compactJet W γ T 1 t x)^4 := by
  unfold secondCurvatureField
  rw [TimeField.generator_add,TimeField.generator_const_mul,TimeField.generator_mul,TimeField.generator_mul,
    curvatureField_generator W γ hT0 hT1,compactJetField_generator_one W γ hT0 hT1,
    compactJetField_generator_two W γ hT0 hT1,curvatureField_deriv W γ hT0 hT1]
  dsimp only [compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1]
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  rw [hc]
  ring

lemma curvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (curvatureField W γ hT0 hT1).f t x=(compactJet W γ T 1 t x)^2 := by
  dsimp only [curvatureField,TimeField.mul,compactJetField]
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
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma thirdCurvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) :
    (thirdCurvatureField W γ hT0 hT1 c).f t x=
      (compactJet W γ T 3 t x)^2-12*c*compactJet W γ T 1 t x*(compactJet W γ T 2 t x)^2+
        6*c^2*(compactJet W γ T 1 t x)^4 := by
  dsimp only [thirdCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

lemma secondCurvatureField_generator_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) (hc : compactCoeff γ T t=c) :
    (secondCurvatureField W γ hT0 hT1 c).generator (compactDrift W γ T) t x=
      (thirdCurvatureField W γ hT0 hT1 c).f t x := by
  rw [thirdCurvatureField_eq]
  exact secondCurvatureField_generator W γ hT0 hT1 c t x hc

end ZeroTemperatureSK

end
end
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

lemma stripThird_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) :
    Continuous (stripThird W γ T c) := TimeField.expected_continuous _ _ _

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

lemma stripSecond_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (c : ℝ) (s : ℝ≥0) (hs : (s:ℝ) < T) (hc : compactCoeff γ T s=c) :
    HasDerivWithinAt (stripSecond W γ T c) (stripThird W γ T c s) (Ioi (s:ℝ)) s := by
  have hd := (secondCurvatureField W γ T.property.1 T.property.2 c).expected_hasDerivWithinAt_right
    (stripDrift W γ T) W s hs (stripDrift_pathDrift_right W γ T s)
  change HasDerivWithinAt (stripSecond W γ T c) _ _ _ at hd
  convert hd using 1 <;> try rfl
  unfold stripThird TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Real.toNNReal_coe,stripDrift]
  exact (secondCurvatureField_generator_eq W γ T.property.1 T.property.2 c (s:ℝ) _ hc).symm

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

lemma stripSecond_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, compactCoeff γ T s=c) :
    HasDerivAt (stripSecond W γ T c) (stripThird W γ T c t) t := by
  apply hasDerivAt_of_right_on_Ioo (stripSecond_continuous W γ T c) (stripThird_continuous W γ T c) ht
  intro s hs
  have hs0 := ha.trans hs.1.le
  have hd := stripSecond_hasDerivWithinAt_right W γ T c (Real.toNNReal s)
    (by rw [Real.coe_toNNReal _ hs0]; exact hs.2.trans_le hbT)
    (by rw [Real.coe_toNNReal _ hs0];exact hc s hs)
  simpa only [Real.coe_toNNReal _ hs0] using hd

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

lemma stripThird_eq_actual (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (htT : t ≤ T) (c : ℝ) :
    stripThird W γ T c t = ∫ ξ, (actualJet W γ t 4 ξ)^2-
      12*c*actualJet W γ t 2 ξ*(actualJet W γ t 3 ξ)^2+6*c^2*(actualJet W γ t 2 ξ)^4 ∂W.law := by
  unfold stripThird TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [thirdCurvatureField_eq]
  have heNN : Real.toNNReal (t:ℝ)=(⟨t,t.property.1⟩:ℝ≥0) := by ext;exact Real.coe_toNNReal _ t.property.1
  rw [heNN]
  have hd := diffusion_eq_strip W γ T (⟨t,t.property.1⟩:ℝ≥0) htT ξ
  rw [← hd,compactJet_eq_value W γ T ⟨t.property.1,htT⟩,
    compactJet_eq_value W γ T ⟨t.property.1,htT⟩,compactJet_eq_value W γ T ⟨t.property.1,htT⟩]
  rfl

lemma actualQuartic_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) : 0 < ∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law := by
  apply actual_jet_even_moment_pos W γ t ht 1 2 (by norm_num)
  have hn := curvature_not_identically_zero W γ t.property.1 t.property.2
  change ∃ x, deriv (deriv (value W γ t)) x ≠ 0 at hn
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hn

lemma stripThird_coercive (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) (hcont : ContinuousAt γ.val t) :
    (1/1000:ℝ)*(γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) ≤
      (γ.val t)^2 * stripThird W γ T (γ.val t) t := by
  have hh := actual_coercivity W γ t ht hcont
  have hl : (∫ ξ, quarticJetPolynomial (γ.val t) (actualJet W γ t 2 ξ) ∂W.law)=
      (γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) := by
    exact integral_const_mul _ _
  have hr : (∫ ξ, coerciveJetPolynomial (γ.val t)
      (actualJet W γ t 2 ξ) (actualJet W γ t 3 ξ) (actualJet W γ t 4 ξ) ∂W.law)=
      (γ.val t)^2 * stripThird W γ T (γ.val t) t := by
    rw [stripThird_eq_actual W γ T t htT,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    unfold coerciveJetPolynomial
    ring
  rw [hl,hr] at hh
  simpa only [mul_assoc] using hh

lemma stripThird_pos (W : BrownianSystem Ω) (γ : OrderParameter) (T t : Time)
    (ht : 0 < (t:ℝ)) (htT : t ≤ T) (hcont : ContinuousAt γ.val t) (hc : 0 < γ.val t) :
    0 < stripThird W γ T (γ.val t) t := by
  have hp := actualQuartic_pos W γ t ht
  have hh := stripThird_coercive W γ T t ht htT hcont
  have hl : 0 < (1/1000:ℝ)*(γ.val t)^4*(∫ ξ, (actualJet W γ t 2 ξ)^4 ∂W.law) := by positivity
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hc)).mp (hl.trans_le hh)

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

lemma OrderParameter.continuousAt_of_constant {γ : OrderParameter} {a b c : ℝ}
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) (t : Time) (ht : (t:ℝ) ∈ Ioo a b) :
    ContinuousAt γ.val t := by
  have hh : γ.val =ᶠ[𝓝 t] fun _ => c := by
    filter_upwards [(continuous_subtype_val.tendsto t).eventually (Ioo_mem_nhds ht.1 ht.2)] with s hs
    have he := hc s hs
    simpa only [extend,dite_eq_left s.property] using he
  exact continuousAt_const.congr_of_eventuallyEq hh

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

lemma curvatureMoment_deriv_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    HasDerivAt (deriv (curvatureMoment W γ)) (stripThird W γ T c t) t := by
  have hd := stripSecond_hasDerivAt_on_constant W γ T ha hbT ht (compactCoeff_constant γ T ha hbT hc)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (curvatureMoment_hasDerivAt_on_constant W γ T ha hbT hs hc).deriv

theorem positive_gap_curvature_oai (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hc0 : 0 < c)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    ∀ t ∈ Ioo a b, 0 < (deriv^[2] (curvatureMoment W γ)) t := by
  intro t ht
  let T : Time := ⟨b,⟨ha.trans hab.le,hb⟩⟩
  have htt : t ∈ Ico (0:ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.trans hb⟩
  let τ : Time := ⟨t,htt⟩
  have he : γ.val τ=c := by simpa only [extend,dite_eq_left htt] using hc t ht
  change 0 < deriv (deriv (curvatureMoment W γ)) t
  rw [(curvatureMoment_deriv_hasDerivAt_on_constant W γ T ha le_rfl ht hc).deriv]
  have hp := stripThird_pos W γ T τ (ha.trans_lt ht.1) ht.2.le
    (γ.continuousAt_of_constant hc τ ht) (by rw [he];exact hc0)
  simpa only [he] using hp

end ZeroTemperatureSK

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ZeroTemperatureSK.positive_gap_curvature_oai.{u_1} := @OAI.ZeroTemperatureSK.positive_gap_curvature_oai.{u_1}
