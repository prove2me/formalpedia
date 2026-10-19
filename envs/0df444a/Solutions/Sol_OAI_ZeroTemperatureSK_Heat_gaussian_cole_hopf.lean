-- Prove2me | solution 1 for OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:27:50.427809+00:00
-- url     : https://prove2.me/submissions/e39b7aba-f0cf-489a-bb14-c2536b0e3c63

import Mathlib
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts

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

lemma integrable_exp_abs (c : ℝ) (μ : ℝ) (h : ℝ≥0) :
    Integrable (fun y : ℝ => Real.exp (c*|y|)) (gaussianReal μ h) := by
  apply Integrable.mono' ((integrable_exp_mul_gaussianReal (μ := μ) (v := h) c).add
    (integrable_exp_mul_gaussianReal (μ := μ) (v := h) (-c)))
    (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hy)]
    have he : c*(-y) = (-c)*y := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.Const
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

lemma standardGaussian_stein {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hg : Integrable g (gaussianReal 0 1)) (hg' : Integrable g' (gaussianReal 0 1))
    (hyg : Integrable (fun y => y*g y) (gaussianReal 0 1)) :
    (∫ y, y*g y ∂gaussianReal 0 1) = ∫ y, g' y ∂gaussianReal 0 1 :=
  (HighDimProb.RandomProcesses.gaussian_integration_by_parts hd hg hg' hyg).symm

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

def ExponentialBound (g : ℝ → ℝ) : Prop :=
  ∃ A K : ℝ≥0, ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|)

lemma integrable_abs_mul_exp_abs (K : ℝ) :
    Integrable (fun y : ℝ => |y| *Real.exp (K*|y|)) (gaussianReal 0 1) := by
  apply Integrable.mono' (integrable_exp_abs (K+1) 0 1) (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |y| *Real.exp (K*|y|) ≤ Real.exp |y| *Real.exp (K*|y|) := by
      gcongr
      linarith [Real.add_one_le_exp |y|]
    _ = Real.exp ((K+1)*|y|) := by rw [← Real.exp_add]; congr 1; ring

lemma exponentialBound_scaled {g : ℝ → ℝ} {A K : ℝ≥0}
    (hg : ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (x a y R : ℝ) (ha : |a| ≤ R) :
    |g (x+a*y)| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*R)*|y|) := by
  calc
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*|x+a*y|) := hg _
    _ ≤ (A:ℝ)*Real.exp ((K:ℝ)*(|x|+R*|y|)) := by
      gcongr
      exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma integrable_scaled_of_expBound {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ExponentialBound g) (a x : ℝ) :
    Integrable (fun y => g (x+a*y)) (gaussianReal 0 1) := by
  obtain ⟨A,K,hg⟩ := hg
  apply Integrable.mono' ((integrable_exp_abs ((K:ℝ)*|a|) 0 1).const_mul
    ((A:ℝ)*Real.exp ((K:ℝ)*|x|)))
    ((hgm.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖g (x+a*y)‖ ≤ _
  simpa only [Real.norm_eq_abs] using exponentialBound_scaled hg x a y |a| le_rfl

lemma integrable_mul_scaled_of_expBound {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ExponentialBound g) (a x : ℝ) :
    Integrable (fun y => y*g (x+a*y)) (gaussianReal 0 1) := by
  obtain ⟨A,K,hg⟩ := hg
  apply Integrable.mono' ((integrable_abs_mul_exp_abs ((K:ℝ)*|a|)).const_mul
    ((A:ℝ)*Real.exp ((K:ℝ)*|x|)))
    ((measurable_id.mul (hgm.comp (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖y*g (x+a*y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |y| *((A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*|a|)*|y|)) := by
      gcongr
      exact exponentialBound_scaled hg x a y |a| le_rfl
    _ = _ := by ring

def scaled (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, g (x+a*y) ∂gaussianReal 0 1

lemma continuous_scaled {g : ℝ → ℝ} (hgc : Continuous g) (hg : ExponentialBound g)
    (x : ℝ) : Continuous (fun a => scaled a g x) := by
  obtain ⟨A,K,hg⟩ := hg
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated
    (bound := fun y => (A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*(|a|+1))*|y|))
  · exact Filter.Eventually.of_forall (fun z => (by fun_prop))
  · filter_upwards [Metric.ball_mem_nhds a (show (0:ℝ)<1 by norm_num)] with z hz
    filter_upwards [] with y
    have hz' : |z| ≤ |a|+1 := by
      have ht := abs_add_le (z-a) a
      rw [sub_add_cancel] at ht
      have hd : |z-a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    simpa only [Real.norm_eq_abs] using exponentialBound_scaled hg x z y (|a|+1) hz'
  · exact (integrable_exp_abs ((K:ℝ)*(|a|+1)) 0 1).const_mul _
  · filter_upwards [] with y
    exact hgc.continuousAt.comp (by fun_prop)

lemma hasDerivAt_scaled {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (a x : ℝ) :
    HasDerivAt (fun z => scaled z g x)
      (∫ y, y*deriv g (x+a*y) ∂gaussianReal 0 1) a := by
  obtain ⟨A,K,hg'⟩ := hg'
  have hdm := hgc.continuous_deriv_one.measurable
  have hm : ∀ᶠ z in 𝓝 a, AEStronglyMeasurable (fun y => g (x+z*y)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall (fun z => by fun_prop)
  have hdmeas : AEStronglyMeasurable (fun y => y*deriv g (x+a*y)) (gaussianReal 0 1) := by fun_prop
  have hb : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball a 1,
      ‖y*deriv g (x+z*y)‖ ≤
        ((A:ℝ)*Real.exp ((K:ℝ)*|x|))*(|y| *Real.exp (((K:ℝ)*(|a|+1))*|y|)) := by
    filter_upwards [] with y z hz
    have hz' : |z| ≤ |a|+1 := by
      have ht := abs_add_le (z-a) a
      rw [sub_add_cancel] at ht
      have hd : |z-a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |y| *((A:ℝ)*Real.exp ((K:ℝ)*|x|)*Real.exp (((K:ℝ)*(|a|+1))*|y|)) := by
        gcongr
        exact exponentialBound_scaled hg' x z y (|a|+1) hz'
      _ = _ := by ring
  have hD : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball a 1,
      HasDerivAt (fun w => g (x+w*y)) (y*deriv g (x+z*y)) z := by
    filter_upwards [] with y z hz
    convert (hgc.differentiable (by norm_num) (x+z*y)).hasDerivAt.comp z
      (((hasDerivAt_id z).mul_const y).const_add x) using 1 <;> first | rfl | simp [mul_comm]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a (show (0:ℝ)<1 by norm_num)) hm
    (integrable_scaled_of_expBound hgc.continuous.measurable hg a x) hdmeas hb
    ((integrable_abs_mul_exp_abs ((K:ℝ)*(|a|+1))).const_mul _) hD).2

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.VarianceHeat
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

lemma hasDerivAt_scaled_second {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) (a x : ℝ) :
    HasDerivAt (fun z => scaled z g x) (a*scaled a (deriv (deriv g)) x) a := by
  have hgd : ContDiff ℝ 1 (deriv g) := hgc.deriv'
  have hs := standardGaussian_stein
    (g := fun y => deriv g (x+a*y))
    (g' := fun y => a*deriv (deriv g) (x+a*y))
    (fun y => by
      convert (hgd.differentiable (by norm_num) (x+a*y)).hasDerivAt.comp y
        (((hasDerivAt_id y).const_mul a).const_add x) using 1 <;> first | rfl | simp [mul_comm])
    (integrable_scaled_of_expBound hgd.continuous.measurable hg' a x)
    ((integrable_scaled_of_expBound hgd.continuous_deriv_one.measurable hg'' a x).const_mul a)
    (integrable_mul_scaled_of_expBound hgd.continuous.measurable hg' a x)
  rw [integral_const_mul] at hs
  exact (hasDerivAt_scaled (hgc.of_le (by norm_num)) hg hg' a x).congr_deriv hs

def varianceHeat (t : ℝ) (g : ℝ → ℝ) (x : ℝ) := scaled (Real.sqrt t) g x

lemma continuous_varianceHeat {g : ℝ → ℝ} (hgc : Continuous g) (hg : ExponentialBound g)
    (x : ℝ) : Continuous (fun t => varianceHeat t g x) :=
  (continuous_scaled hgc hg x).comp Real.continuous_sqrt

lemma hasDerivAt_varianceHeat_pos {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => varianceHeat s g x) ((1/2:ℝ)*varianceHeat t (deriv (deriv g)) x) t := by
  have hd := (hasDerivAt_scaled_second hgc hg hg' hg'' (Real.sqrt t) x).comp t
    (Real.hasDerivAt_sqrt (ne_of_gt ht))
  apply hd.congr_deriv
  change (Real.sqrt t*scaled (Real.sqrt t) (deriv (deriv g)) x)*(1/(2*Real.sqrt t)) = _
  dsimp only [varianceHeat]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]

lemma hasDerivWithinAt_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s g x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv g)) x) (Set.Ici 0) t := by
  by_cases ht0 : t = 0
  · subst t
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    · intro r hr
      exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' hr x).differentiableAt.differentiableWithinAt
    · exact (continuous_varianceHeat hgc.continuous hg x).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · have hc : Continuous (fun r => (1/2:ℝ)*varianceHeat r (deriv (deriv g)) x) :=
        continuous_const.mul (continuous_varianceHeat
          (show Continuous (deriv (deriv g)) from (show ContDiff ℝ 1 (deriv g) from hgc.deriv').continuous_deriv_one)
          hg'' x)
      apply hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' hr x).deriv.symm
  · exact (hasDerivAt_varianceHeat_pos hgc hg hg' hg'' (lt_of_le_of_ne ht (Ne.symm ht0)) x).hasDerivWithinAt

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ZeroTemperatureSK.Foundations.ExponentialBoundLipschitz
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

lemma hasDerivAt_scaled_space {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (a x : ℝ) :
    HasDerivAt (scaled a g) (scaled a (deriv g) x) x := by
  obtain ⟨A,K,hg'⟩ := hg'
  have hdm := hgc.continuous_deriv_one.measurable
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y => g (z+a*y)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall (fun z => by fun_prop)
  have hdmeas : AEStronglyMeasurable (fun y => deriv g (x+a*y)) (gaussianReal 0 1) := by fun_prop
  have hb : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball x 1,
      ‖deriv g (z+a*y)‖ ≤
        ((A:ℝ)*Real.exp ((K:ℝ)*(|x|+1)))*Real.exp (((K:ℝ)*|a|)*|y|) := by
    filter_upwards [] with y z hz
    have hz' : |z| ≤ |x|+1 := by
      have ht := abs_add_le (z-x) x
      rw [sub_add_cancel] at ht
      have hd : |z-x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    rw [Real.norm_eq_abs]
    exact (exponentialBound_scaled hg' z a y |a| le_rfl).trans (by gcongr)
  have hD : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => g (w+a*y)) (deriv g (z+a*y)) z := by
    filter_upwards [] with y z hz
    convert (hgc.differentiable (by norm_num) (z+a*y)).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const (a*y)) using 1 <;> first | rfl | simp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (show (0:ℝ)<1 by norm_num)) hm
    (integrable_scaled_of_expBound hgc.continuous.measurable hg a x) hdmeas hb
    ((integrable_exp_abs ((K:ℝ)*|a|) 0 1).const_mul _) hD).2

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma logarithmic_heat_equation_core {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {c : ℝ} (hc : c ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hpos : ∀ z, 0 < varianceHeat t g z) (x : ℝ) :
    HasDerivWithinAt (fun s => Real.log (varianceHeat s g x)/c)
      ((1/2:ℝ)*deriv (deriv (fun z => Real.log (varianceHeat t g z)/c)) x +
        c/2*(deriv (fun z => Real.log (varianceHeat t g z)/c) x)^2)
      (Set.Ici 0) t := by
  have hdx (z : ℝ) : HasDerivAt (varianceHeat t g) (varianceHeat t (deriv g) z) z :=
    hasDerivAt_scaled_space (hgc.of_le (by norm_num)) hg hg' (Real.sqrt t) z
  have hddx (z : ℝ) : HasDerivAt (varianceHeat t (deriv g))
      (varianceHeat t (deriv (deriv g)) z) z :=
    hasDerivAt_scaled_space (show ContDiff ℝ 1 (deriv g) from hgc.deriv') hg' hg'' (Real.sqrt t) z
  have hdf : deriv (fun z => Real.log (varianceHeat t g z)/c) =
      fun z => (varianceHeat t (deriv g) z/varianceHeat t g z)/c := by
    funext z
    exact ((hdx z).log (ne_of_gt (hpos z)) |>.div_const c).deriv
  have hdd := ((hddx x).div (hdx x) (ne_of_gt (hpos x))).div_const c
  simp only [Pi.div_apply] at hdd
  have htime := ((hasDerivWithinAt_varianceHeat hgc hg hg' hg'' ht x).log
    (ne_of_gt (hpos x))).div_const c
  apply htime.congr_deriv
  rw [hdf, hdd.deriv]
  field_simp [hc, ne_of_gt (hpos x)]
  ring

theorem gaussian_cole_hopf_oai {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ∃ A K : ℝ≥0, ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg' : ∃ A K : ℝ≥0, ∀ z, |deriv g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg'' : ∃ A K : ℝ≥0, ∀ z, |deriv (deriv g) z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    {c : ℝ} (hc : c ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ z, 0 < ∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) (x : ℝ) :
    HasDerivWithinAt
      (fun s => Real.log (∫ y, g (x + Real.sqrt s * y) ∂gaussianReal 0 1) / c)
      ((1/2:ℝ) * deriv (deriv (fun z =>
          Real.log (∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) / c)) x +
        c/2 * (deriv (fun z =>
          Real.log (∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) / c) x)^2)
      (Set.Ici 0) t :=
  logarithmic_heat_equation_core hgc hg hg' hg'' hc ht hpos x

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf_oai := @OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf_oai
