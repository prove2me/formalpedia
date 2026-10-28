-- Prove2me | solution 1 for OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:15:53.598477+00:00
-- url     : https://prove2.me/submissions/99d338ea-8312-41cf-b192-66908b964ab1

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_heatBridge_bounds
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_localized_heatError_tail_bound
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_localized_heat_gradient
import Theorems.Thm_OAI_WeakHessian_cheegerHeat_plan_entropy_dual_error

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
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
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
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

theorem weakGradient_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    weakGradient m f =ᵐ[m] weakGradient (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact weakGradient_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LipschitzDerivQuadraticRemainder
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
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

lemma lipschitzOn_deriv_quadratic_remainder {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    |φ b - φ a - ψ a*(b-a)| ≤ (L:ℝ)*|b-a|^2 := by
  have hseg := hs.segment_subset ha hb
  have H := (convex_segment a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => φ x - φ a - ψ a*(x-a))
    (f' := fun x => ψ x-ψ a) (C := (L:ℝ)*|b-a|)
    (fun x hx => by
      convert ((hφ x (hseg hx)).sub_const (φ a)).sub
        (((hasDerivAt_id x).sub_const a).const_mul (ψ a)) |>.hasDerivWithinAt using 1 <;>
        first | rfl | simp)
    (fun x hx => by
      calc
        ‖ψ x - ψ a‖ ≤ (L:ℝ)*‖x-a‖ := hψ.norm_sub_le (hseg hx) ha
        _ ≤ (L:ℝ)*|b-a| := mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hx) L.coe_nonneg)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using H

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivWithinAt_integral_lipschitzOn {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {S : Set (Lp ℝ 2 m)}
    (hS : ∀ v ∈ S, ∀ᵐ x ∂m, v x ∈ s)
    (hi : ∀ v ∈ S, Integrable (fun x => φ (v x)) m)
    {u : Lp ℝ 2 m} (hu : u ∈ S) (hwu : MemLp (fun x => ψ (u x)) 2 m) :
    HasFDerivWithinAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ (hwu.toLp (fun x => ψ (u x)))) S u := by
  let w : Lp ℝ 2 m := hwu.toLp (fun x => ψ (u x))
  have hw : (w : X → ℝ) =ᵐ[m] fun x => ψ (u x) := MemLp.coeFn_toLp _
  have herr (v : Lp ℝ 2 m) (hv : v ∈ S) :
      |(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ| ≤ (L:ℝ)*‖v-u‖^2 := by
    have hvv : Integrable (fun x => (v-u) x*(v-u) x) m :=
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp (v-u))
    have hn : (∫ x, (v-u) x*(v-u) x ∂m) = ‖v-u‖^2 := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial] using real_inner_self_eq_norm_sq (v-u)
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_sub (hi v hv) (hi u hu)]
    have hii : Integrable (fun x => φ (v x) - φ (u x)) m := (hi v hv).sub (hi u hu)
    rw [← integral_sub hii (show Integrable (fun x => (v-u) x*w x) m from
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp w))]
    calc
      |∫ x, φ (v x) - φ (u x) - (v-u) x * w x ∂m| ≤
          ∫ x, (L:ℝ)*((v-u) x*(v-u) x) ∂m := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hvv.const_mul (L:ℝ))
        filter_upwards [hw,Lp.coeFn_sub v u,hS v hv,hS u hu] with x hx ha hvs hus
        rw [hx,ha]
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        have H := lipschitzOn_deriv_quadratic_remainder hs hφ hψ hus hvs
        rw [sq_abs] at H
        simpa only [pow_two,mul_comm] using H
      _ = (L:ℝ)*‖v-u‖^2 := by rw [integral_const_mul,hn]
  have h0 : Tendsto (fun v : Lp ℝ 2 m => v-u) (𝓝[S] u) (𝓝 0) := by
    simpa only [sub_self,id_eq] using ((tendsto_id : Tendsto (fun v : Lp ℝ 2 m => v) (𝓝 u) (𝓝 u)).mono_left nhdsWithin_le_nhds).sub_const u
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply (IsBigO.of_bound (L:ℝ) ?_).trans_isLittleO
    ((isLittleO_norm_pow_id (show 1 < (2:ℕ) by norm_num)).comp_tendsto h0)
  filter_upwards [eventually_mem_nhdsWithin] with v hv
  change ‖(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ‖ ≤ (L:ℝ)*‖‖v-u‖^2‖
  simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_of_nonneg (norm_nonneg _)] using herr v hv

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivAt_integral_quadratic {φ ψ : ℝ → ℝ} {L : ℝ≥0}
    (hφ : ∀ x, HasDerivAt φ (ψ x) x) (hψ : LipschitzWith L ψ)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ ((hψ.comp_memLp hψ0 (Lp.memLp u)).toLp (ψ ∘ u))) u := by
  have hi (v : Lp ℝ 2 m) : Integrable (fun x => φ (v x)) m := by
    apply ((Lp.memLp v).integrable_sq.const_mul (L:ℝ)).mono'
      ((show Continuous φ from continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
    apply Eventually.of_forall
    intro x
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun x _ => hφ x) hψ.lipschitzOnWith (a := 0) (b := v x) (mem_univ _) (mem_univ _)
    simpa only [hφ0,hψ0,sub_zero,zero_mul,Real.norm_eq_abs,sq_abs] using H
  apply hasFDerivWithinAt_univ.mp
  exact hasFDerivWithinAt_integral_lipschitzOn convex_univ (fun x _ => hφ x) hψ.lipschitzOnWith
    (fun v _ => Eventually.of_forall fun x => mem_univ (v x)) (fun v _ => hi v)
    (mem_univ u) (hψ.comp_memLp hψ0 (Lp.memLp u))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeat
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

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerHeat_bounded (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {B : ℝ} (hB : 0 ≤ B) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ B := by
  have hu' : ∀ᵐ x ∂m, u x ∈ Icc (-B) B := hu.mono fun _ hx => abs_le.mp hx
  exact (cheegerHeat_interval h ht (neg_nonpos.mpr hB) hB u hu').mono fun _ hx => abs_le.mpr hx

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Smul
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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FiniteOnBoundedSets.of_le_smul (hfinite : FiniteOnBoundedSets m) {C : ℝ≥0}
    (hν : ν ≤ (C:ℝ≥0∞) • m) : FiniteOnBoundedSets ν := by
  intro s hs
  have H : (C:ℝ≥0∞)*m s < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite s hs)
  exact lt_of_le_of_lt (hν s) (by simpa only [Measure.smul_apply,smul_eq_mul] using H)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalGradientParallelogram.change_measure (hpar : LocalGradientParallelogram m)
    {C D : ℝ≥0} (hm : m ≤ (C:ℝ≥0∞) • ν) (hν : ν ≤ (D:ℝ≥0∞) • m) :
    LocalGradientParallelogram ν := by
  intro f g hf hg
  have hfm := (localSobolev_iff_of_comparable hm hν f).mpr hf
  have hgm := (localSobolev_iff_of_comparable hm hν g).mpr hg
  apply (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  filter_upwards [hpar f g hfm hgm,weakGradient_eq_of_comparable hm hν f,
    weakGradient_eq_of_comparable hm hν g,
    weakGradient_eq_of_comparable hm hν (fun x => f x+g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x-g x)] with x hp hf hg hplus hminus
  rwa [hf,hg,hplus,hminus] at hp

end WeakHessian

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
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ChangeLpLp
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
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_toLp {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Lp.LpToLpOfMeasureLeSMul hc hν (hf.toLp f) =
      (hf.of_measure_le_smul hc hν).toLp f := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν (hf.toLp f)).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.coeFn_toLp).trans
      (hf.of_measure_le_smul hc hν).coeFn_toLp.symm)

omit [MetricSpace X] [BorelSpace X] in
lemma tendsto_toLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {fs : ℕ → X → ℝ} {f : X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m)
    (h : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ((hfs n).of_measure_le_smul hc hν).toLp (fs n))
      atTop (𝓝 ((hf.of_measure_le_smul hc hν).toLp f)) := by
  have H := (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν).continuous.tendsto _ |>.comp h
  simpa only [Function.comp_def, changeLp_toLp] using H

omit [BorelSpace X] in
lemma FiniteOnBoundedSets.of_measure_le_smul (hm : FiniteOnBoundedSets m)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m) : FiniteOnBoundedSets ν := by
  intro B hB
  exact lt_of_le_of_lt (hν B) (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hm B hB))

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
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyComparable
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

lemma cheegerEnergy_eq_of_comparable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (hfinite : FiniteOnBoundedSets m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D‖^2/2) := by
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 ν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν
  obtain ⟨fs,hLip,hfs,hDs,hf,hG⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  have hfn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hfs (Lp.memLp f)
    (by simpa only [Lp.toLp_coeFn] using hf)
  have hDn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hDs (Lp.memLp D)
    (by simpa only [Lp.toLp_coeFn] using hG)
  have hDf : ((Lp.memLp D).of_measure_le_smul ENNReal.coe_ne_top hν).toLp (D : X → ℝ) = T D := rfl
  rw [hDf] at hDn
  have he : Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂ν) atTop (𝓝 (ENNReal.ofReal (‖T D‖^2/2))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hDn.norm.pow 2).div_const 2)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact half_lintegral_localSlope_eq (hLip n).choose_spec
      ((hDs n).of_measure_le_smul ENNReal.coe_ne_top hν)
  have hle : cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖T D‖^2/2) := by
    have H := cheegerEnergy_le_liminf
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
      (fun n => ⟨hLip n,(hfs n).of_measure_le_smul ENNReal.coe_ne_top hν⟩)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
        (fun n => (hfs n).of_measure_le_smul ENNReal.coe_ne_top hν)
        (f : X → ℝ) ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)).mp hfn)
    rwa [he.liminf_eq] at H
  have hDν : IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (T D) :=
    (hD.change_measure hm hν).congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D).symm
  obtain ⟨D',hD',hlo⟩ := exists_minimalGradient_energy_le_cheeger
    (hfinite.of_measure_le_smul ENNReal.coe_ne_top hν)
    ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have heq : D' = T D := Lp.ext (hD'.ae_eq hDν)
  rw [heq] at hlo
  exact le_antisymm hle hlo

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevCheegerEnergyTop
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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma cheegerEnergy_integral_of_comparable (hfinite : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy ν f = ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂ν)/2) := by
  let f' := hf.1.toLp f
  let D' := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (f' : X → ℝ) (D' : X → ℝ) :=
    (weakGradient_isMinimal hf.2.1.2).congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (f' : X → ℝ) = ENNReal.ofReal (‖D'‖^2/2) := by
    rw [cheegerEnergy_congr_ae hf.1.coeFn_toLp,hID f hf,norm_toLp_sq_eq_integral]
  have H := cheegerEnergy_eq_of_comparable hfinite hm hν hD he
  have ha : (f' : X → ℝ) =ᵐ[ν] f := (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.1.coeFn_toLp
  rw [cheegerEnergy_congr_ae ha] at H
  rw [H]
  congr 2
  let Dν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D'
  have heq : Dν = (hf.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).toLp (weakGradient m f) :=
    changeLp_toLp ENNReal.coe_ne_top hν hf.2.2
  change ‖Dν‖^2 = _
  rw [heq,norm_toLp_sq_eq_integral]

end WeakHessian

end
end InlinedFile0

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

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_energy_le {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    Q (realHeat m hQ.resolventLinear t u) ≤ Q u := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [realHeat_zero m hQ.resolvent_positive]
    rfl
  have hstep {s : ℝ} (hs : 0 < s) (v : Lp ℝ 2 m) :
      Q ((hQ.scale hs).resolventLinear v) ≤ Q v := by
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp
    exact (hQ.scale hs).resolvent_energy_le v
  have hp {s : ℝ} (hs : 0 < s) (n : ℕ) :
      Q ((((hQ.scale hs).resolventLinear)^n) u) ≤ Q u := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        (hstep hs ((((hQ.scale hs).resolventLinear)^n) u)).trans ih
  exact (hQ.lowerSemicontinuous.isClosed_preimage (Q u)).mem_of_tendsto
    (hQ.euler_tendsto_heat m ht u) (Eventually.of_forall fun n => hp (by positivity) (2^n))

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyConst
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

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]

omit [IsFiniteMeasure m] in
lemma cheegerHeat_energy_le (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    cheegerEnergy m (cheegerHeat h t u : X → ℝ) ≤ cheegerEnergy m (u : X → ℝ) :=
  (cheeger_closedQuadraticEnergy h).heat_energy_le m ht u

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_DecayWeight
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
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma densityMeasure_probability_of_integrable (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) (hmass : ∫ x,u x ∂m = 1) :
    IsProbabilityMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hu,hmass,ENNReal.ofReal_one]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_CompressedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma toReal_rnDeriv_bounded {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∀ᵐ x ∂m, |(μ.rnDeriv m x).toReal| ≤ B := by
  filter_upwards [rnDeriv_le_of_le_smul hμ] with x hx
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)

omit [MetricSpace X] [BorelSpace X] in
lemma toReal_rnDeriv_memLp {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    MemLp (fun x => (μ.rnDeriv m x).toReal) 2 m := by
  have hm : AEStronglyMeasurable (fun x => (μ.rnDeriv m x).toReal) m :=
    (μ.measurable_rnDeriv m).ennreal_toReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply ((Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)).const_mul (B : ℝ)).mono' (hm.pow 2)
  filter_upwards [toReal_rnDeriv_bounded hμ] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn : 0 ≤ (μ.rnDeriv m x).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hn] at hx
  simp only [Pi.pow_apply]
  nlinarith

omit [MetricSpace X] [BorelSpace X] in
lemma exists_compressedDensity {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∃ u : Lp ℝ 2 m, (∀ᵐ x ∂m, 0 ≤ u x) ∧ (∀ᵐ x ∂m, |u x| ≤ B) ∧
      Integrable u m ∧ (∫ x, u x ∂m) = μ.real univ ∧
      densityMeasure m u = μ ∧ ‖u‖^2 ≤ (B : ℝ)*μ.real univ := by
  let hd := toReal_rnDeriv_memLp hμ
  let u := hd.toLp (fun x => (μ.rnDeriv m x).toReal)
  have he : (u : X → ℝ) =ᵐ[m] (fun x => (μ.rnDeriv m x).toReal) := hd.coeFn_toLp
  have hn : ∀ᵐ x ∂m, 0 ≤ u x := he.mono fun _ hx => hx ▸ ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂m, |u x| ≤ B := by
    filter_upwards [he,toReal_rnDeriv_bounded hμ] with x hx hb
    rwa [hx]
  have hi : Integrable u m := Measure.integrable_toReal_rnDeriv.congr he.symm
  have hac : μ ≪ m := Measure.absolutelyContinuous_of_le_smul hμ
  have hmass : (∫ x, u x ∂m) = μ.real univ :=
    (integral_congr_ae he).trans (Measure.integral_toReal_rnDeriv hac)
  refine ⟨u,hn,hb,hi,hmass,?_,?_⟩
  · calc
      densityMeasure m u = m.withDensity (μ.rnDeriv m) := by
        apply withDensity_congr_ae
        filter_upwards [he,Measure.rnDeriv_ne_top μ m] with x hx ht
        rw [hx,ENNReal.ofReal_toReal ht]
      _ = μ := Measure.withDensity_rnDeriv_eq μ m hac
  · have hs : ‖u‖^2 = ∫ x, (u x)^2 ∂m := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      congr 1; funext x
      simp only [RCLike.inner_apply,conj_trivial,pow_two]
    rw [hs,← hmass,← integral_const_mul]
    apply integral_mono_ae (Lp.memLp u).integrable_sq (hi.const_mul (B : ℝ))
    filter_upwards [hn,hb] with x hn hb
    rw [abs_of_nonneg hn] at hb
    nlinarith

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile75
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma integral_densityMeasure_L2 (u f : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    (∫ x,f x ∂densityMeasure m u) = ⟪f,u⟫_ℝ := by
  rw [integral_densityMeasure,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  exact hun

end WeakHessian

end
end InlinedFile75

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_AveragedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_timeAverageEval (s : ℝ) :
    Continuous (fun z : ℝ × Curve X => evalReal z.2 (s-z.1)) :=
  continuous_evalReal.comp (continuous_snd.prodMk (continuous_const.sub continuous_fst))

omit [SigmaFinite m] in
lemma IsTestPlan.timeAverageLaw_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    timeAverageLaw π ν s ≤ (B : ℝ≥0∞) • m := by
  let : IsProbabilityMeasure π := hπ.1
  apply Measure.le_iff.mpr
  intro S hS
  rw [timeAverageLaw,Measure.map_apply (continuous_timeAverageEval s).measurable hS,
    Measure.prod_apply (hS.preimage (continuous_timeAverageEval s).measurable)]
  calc
    _ ≤ ∫⁻ _r, ((B : ℝ≥0∞) • m) S ∂ν := by
      apply lintegral_mono
      intro r
      simpa only [Measure.map_apply (continuous_eval_const (clampTime (s-r))).measurable hS,
        preimage_preimage,Function.comp_def,evalReal] using (hB (clampTime (s-r))) S
    _ = _ := by simp

lemma isProbabilityMeasure_timeAverageLaw (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    IsProbabilityMeasure (timeAverageLaw π ν s) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_timeAverageEval s).measurable.aemeasurable).mpr inferInstance

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma integrable_shiftedDensity {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun r => u (clampTime (s-r))) ν := by
  apply Integrable.of_bound
    ((hu.comp_measurable (continuous_clampTime.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable)
    ((B : ℝ)+1)
  filter_upwards [] with r
  change ‖u (clampTime (s-r))‖ ≤ (B : ℝ)+1
  have hb := hB (clampTime (s-r))
  have hn := norm_nonneg (u (clampTime (s-r)))
  have hB0 := B.coe_nonneg
  nlinarith [sq_nonneg (‖u (clampTime (s-r))‖-1)]

omit [SigmaFinite m] in
lemma timeAverageLaw_density_pairing
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) (f : Lp ℝ 2 m) :
    (∫ x, f x ∂timeAverageLaw π ν s) = ∫ r, ⟪f,u (clampTime (s-r))⟫_ℝ ∂ν := by
  let : IsProbabilityMeasure π := hπ.1
  let := isProbabilityMeasure_timeAverageLaw π ν s
  have hle := hπ.timeAverageLaw_le hB ν s
  have hf : Integrable f (timeAverageLaw π ν s) :=
    MemLp.integrable (by norm_num) (((Lp.memLp f).smul_measure ENNReal.coe_ne_top).mono_measure hle)
  have hprod : Integrable (fun z : ℝ × Curve X => f (evalReal z.2 (s-z.1))) (ν.prod π) :=
    (integrable_map_measure hf.1 (continuous_timeAverageEval s).measurable.aemeasurable).mp hf
  rw [timeAverageLaw,integral_map (continuous_timeAverageEval s).measurable.aemeasurable hf.1,
    integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← integral_densityMeasure_L2 _ _ (hun (clampTime (s-r))),hlaw]
  exact (integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
    ((Lp.memLp f).aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))).symm

lemma IsTestPlan.exists_timeAverageDensity
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    let w := ∫ r, u (clampTime (s-r)) ∂ν
    (∀ᵐ x ∂m, 0 ≤ w x) ∧ (∀ᵐ x ∂m, |w x| ≤ B) ∧
      Integrable w m ∧ (∫ x, w x ∂m) = 1 ∧
      densityMeasure m w = timeAverageLaw π ν s ∧ ‖w‖^2 ≤ (B : ℝ) := by
  let : IsProbabilityMeasure π := hπ.1
  let := isProbabilityMeasure_timeAverageLaw π ν s
  obtain ⟨w,hwn,hwb,hwi,hwm,hwl,hwnorm⟩ := exists_compressedDensity (hπ.timeAverageLaw_le hB ν s)
  have he : (∫ r, u (clampTime (s-r)) ∂ν) = w := by
    apply ext_inner_left ℝ
    intro f
    change (innerSL ℝ f) (∫ r, u (clampTime (s-r)) ∂ν) = ⟪f,w⟫_ℝ
    rw [← (innerSL ℝ f).integral_comp_comm (integrable_shiftedDensity hu hnorm ν s),
      ← integral_densityMeasure_L2 _ _ hwn,hwl]
    exact (timeAverageLaw_density_pairing hπ hB hun hlaw ν s f).symm
  dsimp only
  rw [he]
  refine ⟨hwn,hwb,hwi,?_,hwl,?_⟩
  · simpa [Measure.real] using hwm
  · simpa [Measure.real] using hwnorm

end WeakHessian

end
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
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.restrict_reference_of_tracks {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ᵐ γ ∂π, ∀ t : Time, γ t ∈ S) : IsTestPlan (m.restrict S) π := by
  refine ⟨hπ.1,?_,hπ.2.2⟩
  obtain ⟨C,hC⟩ := hπ.2.1
  refine ⟨C,fun t => ?_⟩
  have ha : ∀ᵐ x ∂(π.map (fun γ => γ t)), x ∈ S :=
    (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hS).mpr
      (hs.mono fun γ hγ => hγ t)
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  convert Measure.restrict_mono le_rfl (hC t) using 1
  all_goals try with_reducible_and_instances rfl
  exact (Measure.restrict_smul _ _ _).symm

lemma IsTestPlan.ball_localization {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) :
    ∃ o : X, ∃ R : ℝ, 0 < R ∧ IsTestPlan (m.restrict (Metric.ball o R)) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  refine ⟨o,R+1,by linarith,hπ.restrict_reference_of_tracks measurableSet_ball ?_⟩
  filter_upwards [hb] with γ hγ t
  exact (hγ t).trans_lt (by linarith)

lemma IsTestPlan.continuous_integral_eval_local (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R))) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact hplan.continuous_integral_eval (hf o R hR)

end WeakHessian

end
end InlinedFile1

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_DensityCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory TopologicalSpace WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

lemma norm_lowerSemicontinuous_of_inner_continuous
    {T H : Type*} [TopologicalSpace T] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : T → H} (hu : ∀ f : H, Continuous (fun t => ⟪u t,f⟫_ℝ)) :
    LowerSemicontinuous (fun t => ‖u t‖) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : 0 ≤ r
  · have he : (fun t => ‖u t‖) ⁻¹' Iic r =
        ⋂ f : H, {t | ⟪u t,f⟫_ℝ ≤ r*‖f‖} := by
      ext t
      simp only [mem_preimage,mem_Iic,mem_iInter,mem_ofPred_eq]
      constructor
      · intro ht f
        exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      · intro ht
        have h := ht (u t)
        rw [real_inner_self_eq_norm_sq,pow_two] at h
        by_cases hz : ‖u t‖ = 0
        · rwa [hz]
        · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp h
    rw [he]
    exact isClosed_iInter fun f => isClosed_le (hu f) continuous_const
  · have he : (fun t => ‖u t‖) ⁻¹' Iic r = ∅ := by
      ext t
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hr) (norm_nonneg _))
    rw [he]; exact isClosed_empty

lemma stronglyMeasurable_of_inner_continuous
    {T H : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    {u : T → H} (hu : ∀ f : H, Continuous (fun t => ⟪u t,f⟫_ℝ)) :
    StronglyMeasurable u := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have hb : IsTopologicalBasis {s : Set H | ∃ x r, s = Metric.ball x r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨x,r,rfl⟩; exact Metric.isOpen_ball
    · intro x s hx hs
      obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hs x hx
      exact ⟨Metric.ball x r,⟨x,r,rfl⟩,Metric.mem_ball_self hr,hsub⟩
  have hm : Measurable u := by
    change @Measurable T H _ (borel H) u
    rw [hb.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro s ⟨x,r,rfl⟩
    have hl : LowerSemicontinuous (fun t => ‖u t-x‖) :=
      norm_lowerSemicontinuous_of_inner_continuous fun f => by
        convert (hu f).sub (continuous_const (y := ⟪x,f⟫_ℝ)) using 1
        all_goals try with_reducible_and_instances rfl
        funext t
        simp only [inner_sub_left,Pi.sub_apply]
    convert hl.measurable (measurableSet_Iio (a := r)) using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp [Metric.mem_ball,dist_eq_norm]
  exact hm.stronglyMeasurable

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsTestPlan.continuous_density_inner (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {u : Time → Lp ℝ 2 m} (hu : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t)) (f : Lp ℝ 2 m) :
    Continuous (fun t => ⟪u t,f⟫_ℝ) := by
  have he (t : Time) : ⟪u t,f⟫_ℝ = ∫ γ, f (γ t) ∂π := by
    rw [real_inner_comm,← integral_densityMeasure_L2 _ _ (hu t),hlaw t]
    apply integral_map (continuous_eval_const t).measurable.aemeasurable
    obtain ⟨B,hB⟩ := hπ.2.1
    exact (Lp.memLp f).aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB t))
  simp_rw [he]
  apply hπ.continuous_integral_eval_local hfin hb
  intro o R hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).integrable (by norm_num)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ExplicitDensityNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma IsTestPlan.exists_L2_density_curve_bound (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m) :
    ∃ u : Time → Lp ℝ 2 m, StronglyMeasurable u ∧
      (∀ t, ∀ᵐ x ∂m,0 ≤ u t x) ∧ (∀ t, ∀ᵐ x ∂m,|u t x| ≤ B) ∧
      (∀ t,Integrable (u t) m) ∧ (∀ t,∫ x,u t x ∂m = 1) ∧
      (∀ t,densityMeasure m (u t) = π.map (fun γ => γ t)) ∧
      (∀ t,‖u t‖^2 ≤ (B : ℝ)) := by
  classical
  let : IsProbabilityMeasure π := hπ.1
  choose u hun hub hui hum hul hunorm using fun t => exists_compressedDensity (hB t)
  have hm (t : Time) : ∫ x,u t x ∂m = 1 := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hum t
  have hnorm (t : Time) : ‖u t‖^2 ≤ (B : ℝ) := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hunorm t
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hc := hπ.continuous_density_inner hfin hb hun hul
  exact ⟨u,stronglyMeasurable_of_inner_continuous hc,hun,hub,hui,hm,hul,hnorm⟩

omit [MetricSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma norm_toLp_sq_le_smul_measure {ν : Measure X} {C : ℝ≥0}
    (hν : ν ≤ (C : ℝ≥0∞) • m) {f : X → ℝ} (hf : MemLp f 2 m)
    (hfν : MemLp f 2 ν) :
    ‖hfν.toLp f‖^2 ≤ (C:ℝ)*‖hf.toLp f‖^2 := by
  rw [norm_toLp_sq_eq_integral,norm_toLp_sq_eq_integral]
  have H := integral_mono_measure hν (ae_of_all _ fun x => sq_nonneg (f x))
    (hf.integrable_sq.smul_measure ENNReal.coe_ne_top)
  simpa only [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul] using H

lemma norm_toLp_le_smul_measure_loose {ν : Measure X} {C : ℝ≥0}
    (hC : (1:ℝ) ≤ C) (hν : ν ≤ (C : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : MemLp f 2 m) (hfν : MemLp f 2 ν) :
    ‖hfν.toLp f‖ ≤ (C:ℝ)*(‖hf.toLp f‖+1) := by
  have H := norm_toLp_sq_le_smul_measure hν hf hfν
  have hC0 := C.coe_nonneg
  have hfn := norm_nonneg (hf.toLp f)
  have hfnν := norm_nonneg (hfν.toLp f)
  have HC : (C:ℝ) ≤ (C:ℝ)^2 := by nlinarith
  have Hsq := mul_le_mul_of_nonneg_right HC (sq_nonneg ‖hf.toLp f‖)
  have Hsq' : (C:ℝ)^2*‖hf.toLp f‖^2 ≤ ((C:ℝ)*(‖hf.toLp f‖+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg (C:ℝ)) hfn]
  exact (sq_le_sq₀ hfnν (by positivity)).mp (H.trans (Hsq.trans Hsq'))

lemma norm_product_of_compression {ν : Measure X} {E B : ℝ≥0}
    (hE : (1:ℝ) ≤ E) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {ξ : Lp ℝ 2 ν} (hξ : ‖ξ‖^2 ≤ (B:ℝ)*(E:ℝ))
    {f : X → ℝ} (hf : MemLp f 2 m) (hfν : MemLp f 2 ν) :
    ‖ξ‖*‖hfν.toLp f‖ ≤ ((B:ℝ)+1)*(‖hf.toLp f‖+1)*(E:ℝ)^2 := by
  have hξn := norm_nonneg ξ
  have hB := B.coe_nonneg
  have hEn := E.coe_nonneg
  have hξb : ‖ξ‖ ≤ ((B:ℝ)+1)*(E:ℝ) := by
    apply (sq_le_sq₀ hξn (by positivity)).mp
    apply hξ.trans
    have h1 : (B:ℝ) ≤ ((B:ℝ)+1)^2 := by nlinarith [sq_nonneg (B:ℝ)]
    have h2 : (E:ℝ) ≤ (E:ℝ)^2 := by nlinarith
    have H := mul_le_mul h1 h2 hEn (sq_nonneg ((B:ℝ)+1))
    simpa only [mul_pow] using H
  have H := mul_le_mul hξb (norm_toLp_le_smul_measure_loose hE hν hf hfν)
    (norm_nonneg _) (by positivity : 0 ≤ ((B:ℝ)+1)*(E:ℝ))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

end WeakHessian

end
end

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

end WeakHessian

end

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

lemma regularizedEntropy_zero (a : ℝ) : regularizedEntropy a 0 = 0 := by
  simp [regularizedEntropy]
lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]

lemma regularizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedEntropy a) (regularizedLog a x) x := by
  have hc := (regularizedLog_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-(Real.log a+1)*x := by
  let F : ℝ → ℝ := fun y => (y+a)*Real.log (y+a)-(Real.log a+1)*y
  have hF (y : ℝ) (hy : y ∈ uIcc 0 x) : HasDerivAt F (regularizedLog a y) y := by
    rw [uIcc_of_le hx] at hy
    have hypos : 0 < y+a := by linarith [hy.1]
    have H := ((Real.hasDerivAt_mul_log hypos.ne').comp y ((hasDerivAt_id y).add_const a)).sub
      ((hasDerivAt_id y).const_mul (Real.log a+1))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    rw [regularizedLog_eq ha hy.1]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((regularizedLog_contDiff ha).continuous.intervalIntegrable 0 x)
  change regularizedEntropy a x = F x-F 0 at H
  rw [H]
  dsimp [F]
  ring_nf

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma regularizedEntropy_hasFDeriv {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, regularizedEntropy a (v x) ∂m)
      (innerSL ℝ ((regularizedLog_memLp ha u).toLp (fun x => regularizedLog a (u x)))) u :=
  hasFDerivAt_integral_quadratic (regularizedEntropy_hasDeriv ha) (regularizedLog_lipschitz ha)
    (regularizedEntropy_zero a) (regularizedLog_zero a) u

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RegularizedEntropyIntegrable
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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma regularizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    Integrable (fun x => regularizedEntropy a (u x)) m := by
  apply ((Lp.memLp u).integrable_sq.const_mul a⁻¹).mono'
    ((show Continuous (regularizedEntropy a) from continuous_iff_continuousAt.mpr
      (fun y => (regularizedEntropy_hasDeriv ha y).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun y _ => regularizedEntropy_hasDeriv ha y) (regularizedLog_lipschitz ha).lipschitzOnWith
      (a := 0) (b := u x) (mem_univ _) (mem_univ _)
    simpa only [regularizedEntropy_zero,regularizedLog_zero,zero_mul,sub_zero,Real.norm_eq_abs,sq_abs,NNReal.coe_mk] using! H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RenormalizedEntropy
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
open scoped Topology

lemma renormalizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    renormalizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-x := by
  rw [renormalizedEntropy,regularizedEntropy_eq ha hx]
  ring

lemma renormalizedEntropy_lower {a x w : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hw : 0 < w) :
    x*Real.log w-w ≤ renormalizedEntropy a x := by
  by_cases hz : x = 0
  · simp only [hz,renormalizedEntropy,regularizedEntropy_zero,mul_zero,zero_add,zero_mul,zero_sub]
    linarith
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have H := Real.log_le_sub_one_of_pos (div_pos hw hxp)
  rw [Real.log_div hw.ne' hxp.ne'] at H
  have HH := mul_le_mul_of_nonneg_left H hx
  have hdiv : x*(w/x-1)=w-x := by field_simp
  rw [hdiv] at HH
  have hxlog := mul_le_mul_of_nonneg_left (Real.log_le_log hxp (le_add_of_nonneg_right ha.le)) hx
  have halog := mul_le_mul_of_nonneg_left (Real.log_le_log ha (le_add_of_nonneg_left hx)) ha.le
  rw [renormalizedEntropy_eq ha hx]
  nlinarith

lemma renormalizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (renormalizedEntropy a) (regularizedLog a x+Real.log a) x := by
  simpa only [renormalizedEntropy,Pi.add_apply,id_eq,mul_one] using! (regularizedEntropy_hasDeriv ha x).add
    ((hasDerivAt_id x).const_mul (Real.log a))

lemma renormalizedEntropy_upper {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    renormalizedEntropy a x ≤ x^2/2 := by
  let F (y : ℝ) := renormalizedEntropy a y-y^2/2
  have hd (y : ℝ) : HasDerivAt F (regularizedLog a y+Real.log a-y) y := by
    convert! (renormalizedEntropy_hasDeriv ha y).sub (((hasDerivAt_id y).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (simp only [id_eq]; ring)
  have H : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Ici 0)
      rw [regularizedLog_eq ha hy0]
      have HH := Real.log_le_sub_one_of_pos (by linarith : 0 < y+a)
      linarith
  have HH := H (show (0:ℝ) ∈ Ici 0 from (by simp)) hx hx
  have hF0 : F 0 = 0 := by simp [F,renormalizedEntropy,regularizedEntropy_zero]
  rw [hF0] at HH
  dsimp [F] at HH
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherEpsilon
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
open scoped Topology ENNReal NNReal

lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_le_one (n : ℕ) : fisherEpsilon n ≤ 1 := by
  unfold fisherEpsilon
  exact (div_le_one (by positivity)).mpr (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RadialEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile30
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma squareDensity_entropy_eq [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    entropyReal m (squareDensityMeasure m w) = ∫ x,w x^2*Real.log (w x^2) ∂m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density hac]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

end WeakHessian

end
end InlinedFile30

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropy
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
open scoped Topology NNReal ENNReal

lemma renormalizedEntropy_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => renormalizedEntropy (fisherEpsilon n) x) atTop (𝓝 (reducedEntropy x)) := by
  have h1 := Real.continuous_mul_log.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x)).add fisherEpsilon_tendsto)
  have h2 := Real.continuous_mul_log.continuousAt.tendsto.comp fisherEpsilon_tendsto
  convert! (h1.sub h2).sub_const x using 1
  · ext n
    exact renormalizedEntropy_eq (fisherEpsilon_pos n) hx
  · simp only [reducedEntropy,add_zero,zero_mul,sub_zero]

lemma renormalizedEntropy_abs_bound {a x V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    |renormalizedEntropy a x| ≤ x^2/2+|x*V|+Real.exp (-V) := by
  have hl := renormalizedEntropy_lower ha hx (Real.exp_pos (-V))
  rw [Real.log_exp,mul_neg] at hl
  have hu := renormalizedEntropy_upper ha ha1 hx
  exact abs_le.mpr ⟨by linarith [le_abs_self (x*V),sq_nonneg x],
    by linarith [abs_nonneg (x*V),Real.exp_pos (-V)]⟩

lemma reducedEntropy_abs_bound {x V : ℝ} (hx : 0 ≤ x) :
    |reducedEntropy x| ≤ x^2/2+|x*V|+Real.exp (-V) :=
  le_of_tendsto ((renormalizedEntropy_tendsto hx).abs)
    (Eventually.of_forall (fun n => renormalizedEntropy_abs_bound (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply (((hu.integrable_sq.div_const 2).add hUV.norm).add hV).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [hun] with x hx
  simpa only [Real.norm_eq_abs,Pi.add_apply,reducedEntropy,Pi.sub_apply,id_eq] using! reducedEntropy_abs_bound (V := V x) hx

lemma tendsto_integral_renormalizedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => u x^2/2+‖u x*V x‖+Real.exp (-V x))
  · intro n
    exact (continuous_iff_continuousAt.mpr fun y =>
      (renormalizedEntropy_hasDeriv (fisherEpsilon_pos n) y).continuousAt).comp_aestronglyMeasurable hu.aestronglyMeasurable
  · exact ((hu.integrable_sq.div_const 2).add hUV.norm).add hV
  · intro n
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs] using renormalizedEntropy_abs_bound (V := V x)
      (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx
  · exact hun.mono (fun x hx => renormalizedEntropy_tendsto hx)
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_InitialHeatLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_mul_tendsto_L2 {ι : Type*} {l : Filter ι}
    {u : ι → Lp ℝ 2 m} {v : Lp ℝ 2 m} (hu : Tendsto u l (𝓝 v))
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n => ∫ x, u n x*f x ∂m) l (𝓝 (∫ x, v x*f x ∂m)) := by
  let F : Lp ℝ 2 m := hf.toLp f
  have hp (w : Lp ℝ 2 m) : (∫ x, w x*f x ∂m) = ⟪F,w⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [F,hx,RCLike.inner_apply,RCLike.conj_to_real]
  simp_rw [hp]
  exact tendsto_const_nhds.inner hu

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_tendsto_nonneg
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hθ : Tendsto θ l (𝓝 t)) (hn : ∀ᶠ i in l, 0 ≤ θ i) :
    Tendsto (fun i => cheegerHeat h (θ i) u) l (𝓝 (cheegerHeat h t u)) :=
  ((cheegerHeat_continuousOn hfin h u) t ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hθ,hn⟩)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_GeneratorSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile46
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_eq_square_sqrt (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) :
    densityMeasure m u = squareDensityMeasure m (fun x => Real.sqrt (u x)) := by
  apply withDensity_congr_ae
  filter_upwards [hun] with x hx
  rw [Real.sq_sqrt hx]

end WeakHessian

end
end InlinedFile46

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEVI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile51
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma entropyReal_eq_reducedDensity (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hi : Integrable u m) (hr : Integrable (fun x => reducedEntropy (u x)) m)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u) :
    entropyReal m (μ:Measure X) = (∫ x,reducedEntropy (u x) ∂m)+1 := by
  have hmass : (∫ x,u x ∂m) = 1 := by
    have H := integral_densityMeasure m u hun (fun _ => (1:ℝ))
    rw [← hμ] at H
    simpa using H.symm
  have he := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_entropy_eq (Lp.stronglyMeasurable u |>.measurable.sqrt),← hmass,← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,reducedEntropy,sub_add_cancel]

end WeakHessian

end
end InlinedFile51

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_StrongEntropyConfinement
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
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.exists_strong_entropy_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  let d := |C|+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hCd : C < d := by dsimp [d]; linarith [le_abs_self C]
  have hvol := cd_ball_volume_bound hN hcd hfull hfin o
  have hbase : MemLp (fun x => Real.exp (-(d*dist x o))) 2 m := by
    simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le
      (show C < 2*d by linarith) hvol
  have hbI : Integrable (fun x => Real.exp (-(d*dist x o))) m := by
    simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le hCd hvol
  refine ⟨2*d,by positivity,?_,?_,?_,?_,?_⟩
  · simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*d by linarith) hvol
  · simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*(2*d) by linarith) hvol
  · apply (hbase.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*d*dist x o)*Real.exp (-(2*d*dist x o))| ≤ |2*Real.exp (-(d*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      have H := (Real.mul_exp_neg_le_exp_neg_one (d*dist x o)).trans
        (show Real.exp (-1) ≤ 1 by rw [Real.exp_le_one_iff]; norm_num)
      have he : (2*d*dist x o)*Real.exp (-(2*d*dist x o)) =
          2*(d*dist x o*Real.exp (-(d*dist x o)))*Real.exp (-(d*dist x o)) := by
        rw [show -(2*d*dist x o) = -(d*dist x o)+(-(d*dist x o)) by ring,Real.exp_add]
        ring
      rw [he]
      nlinarith [Real.exp_pos (-(d*dist x o))]
  · convert! hbase using 1; funext x; congr 1; ring
  · convert! hbI using 1; funext x; congr 1; ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LipschitzMulDist
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
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_mul_dist (o : X) (a : ℝ) :
    LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |a*dist x o-a*dist y o| ≤ |a| * dist x y
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile181
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2) := by
  rw [hrcd.1.global_cheegerEnergy_eq_weakGradient hfin o hf,norm_toLp_sq_eq_integral]

omit [SigmaFinite m] in
lemma RCD.weighted_cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B)
    {f : X → ℝ} (hf : Sobolev (exponentialMeasure m V) f) :
    cheegerEnergy (exponentialMeasure m V) f =
      ENNReal.ofReal ((∫ x,(weakGradient (exponentialMeasure m V) f x)^2
        ∂exponentialMeasure m V)/2) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hfm := (sobolev_exponentialMeasure_iff hB f).mpr hf
  have H := cheegerEnergy_integral_of_comparable hfin
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν hfm
  rw [H]
  congr 2
  apply integral_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (weakGradient_exponentialMeasure (m := m) hB f)] with x hx
  rw [hx]

end WeakHessian

end
end InlinedFile181

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_FormAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma weighted_gradient_add_smul (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {ρ : X → ℝ} (hρm : AEStronglyMeasurable ρ m) {B : ℝ}
    (hρb : ∀ᵐ x ∂m, |ρ x| ≤ B) (c : ℝ) :
    (∫ x, ρ x*(weakGradient m (f+c•g : Lp ℝ 2 m) x)^2 ∂m) =
      (∫ x, ρ x*(weakGradient m f x)^2 ∂m) +
      2*c*(∫ x, ρ x*gamma m f g x ∂m) +
      c^2*(∫ x, ρ x*(weakGradient m g x)^2 ∂m) := by
  have hfe : Integrable (fun x => ρ x*(weakGradient m f x)^2) m :=
    hf.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hge : Integrable (fun x => ρ x*(weakGradient m g x)^2) m :=
    hg.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hfge : Integrable (fun x => ρ x*gamma m f g x) m :=
    (integrable_gamma hfin hf hg).bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hre : (f+c•g : Lp ℝ 2 m) =ᵐ[m] (fun x => f x+c*g x) := by
    filter_upwards [Lp.coeFn_add f (c•g),Lp.coeFn_smul c g] with x ha hc
    simp only [ha,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ∫ x, ρ x*(weakGradient m f x)^2+
        2*c*(ρ x*gamma m f g x)+c^2*(ρ x*(weakGradient m g x)^2) ∂m := by
      apply integral_congr_ae
      filter_upwards [weakGradient_congr_ae hre,
        weakGradient_linear_combination_sq hfin hpar hf.2.1 hg.2.1 c] with x hre hx
      rw [hre,hx]; ring
    _ = _ := by
      have h1 := integral_add (hfe.add (hfge.const_mul (2*c))) (hge.const_mul (c^2))
      have h2 := integral_add hfe (hfge.const_mul (2*c))
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2,integral_const_mul,integral_const_mul]

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_SmoothDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma kernelMeasure_probability {κ : ℝ → ℝ} (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) : IsProbabilityMeasure (kernelMeasure κ) := by
  constructor
  rw [kernelMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn),hm]
  simp

lemma integral_kernelMeasure {κ : ℝ → ℝ} (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ r, f r ∂kernelMeasure κ) = ∫ r, κ r • f r := by
  rw [kernelMeasure,integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _)]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_eq_average {κ : ℝ → ℝ} (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r)
    (u : Time → Lp ℝ 2 m) (s : ℝ) :
    smoothDensity κ u s = ∫ r, u (clampTime (s-r)) ∂kernelMeasure κ := by
  rw [integral_kernelMeasure hc hn]
  rfl

lemma IsTestPlan.smoothDensity_properties
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hc : Continuous κ) (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) :
    (∀ᵐ x ∂m, 0 ≤ smoothDensity κ u s x) ∧
      (∀ᵐ x ∂m, |smoothDensity κ u s x| ≤ B) ∧
      Integrable (smoothDensity κ u s) m ∧ (∫ x, smoothDensity κ u s x ∂m) = 1 ∧
      densityMeasure m (smoothDensity κ u s) = timeAverageLaw π (kernelMeasure κ) s ∧
      ‖smoothDensity κ u s‖^2 ≤ (B : ℝ) := by
  let := kernelMeasure_probability hi hn hm
  rw [smoothDensity_eq_average hc hn]
  exact hπ.exists_timeAverageDensity hB hu hun hlaw hnorm (kernelMeasure κ) s

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma planKineticCost_nonneg (π : Measure (Curve X)) : 0 ≤ planKineticCost π :=
  integral_nonneg fun _ => sq_nonneg _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_PlanHeatEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma backwardsHeatTime_pos {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (s : ℝ) :
    0 < backwardsHeatTime δ T s := by
  dsimp [backwardsHeatTime]
  exact add_pos_of_pos_of_nonneg hδ (mul_nonneg hT (le_max_right _ _))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropyDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_renormalizedEntropy_eq (u : Lp ℝ 2 m) (hu : Integrable u m)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x,renormalizedEntropy ε (u x) ∂m) =
      (∫ x,regularizedEntropy ε (u x) ∂m)+Real.log ε*(∫ x,u x ∂m) := by
  simp only [renormalizedEntropy]
  rw [integral_add (regularizedEntropy_integrable hε u) (hu.const_mul _),integral_const_mul]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma tendsto_regularizedEntropy_difference (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => (∫ x,regularizedEntropy (fisherEpsilon n) (u x) ∂m)-
      (∫ x,regularizedEntropy (fisherEpsilon n) (v x) ∂m)) atTop
      (𝓝 ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (v x) ∂m))) := by
  have H := (tendsto_integral_renormalizedEntropy (Lp.memLp u) hun huV hV).sub
    (tendsto_integral_renormalizedEntropy (Lp.memLp v) hvn hvV hV)
  simpa only [integral_renormalizedEntropy_eq u hu (fisherEpsilon_pos _),
    integral_renormalizedEntropy_eq v hv (fisherEpsilon_pos _),hm,add_sub_add_right_eq_sub] using H

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma entropy_dual_of_regularized (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m)
    {A B T D : ℝ} (hd : ∀ ε : ℝ,0 < ε →
      A+T*((∫ x,regularizedEntropy ε (u x) ∂m)-
        (∫ x,regularizedEntropy ε (v x) ∂m)) ≤ B+ε*D) :
    A+T*((∫ x,reducedEntropy (u x) ∂m)-
      (∫ x,reducedEntropy (v x) ∂m)) ≤ B := by
  have H := le_of_tendsto_of_tendsto
    ((tendsto_regularizedEntropy_difference u v hu hv hm hun hvn huV hvV hV).const_mul T |>.const_add A)
    (fisherEpsilon_tendsto.mul_const D |>.const_add B)
    (Eventually.of_forall fun n => hd (fisherEpsilon n) (fisherEpsilon_pos n))
  simpa only [zero_mul,add_zero] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma heatBridgeError_const (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (c T s : ℝ) :
    heatBridgeError h f ξ (fun _ => c) T s = c*heatBridgeEnergy h f ξ T s := by
  dsimp [heatBridgeError,heatBridgeEnergy]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

lemma heatBridgeEnergy_zero (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T 0 = ∫ x,ξ x*gamma m (cheegerHeat h T f) (cheegerHeat h T f) x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

lemma heatBridgeEnergy_end (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T T = ∫ x,cheegerHeat h T ξ x*gamma m f f x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_IdentifiedConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile216
noncomputable section
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma identified_cheegerResolvent_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖(identified_cheegerResolvent_weighted hID hpar hfinite o h u ht hV hU hsmall).toLp
      (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x))‖ ≤ ‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2) := by
  have H := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
    (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) (by
      intro n
      have HD := identified_cheegerResolvent_davies hID hpar hfinite o h u ht (hV.min_const (n:ℝ))
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
      have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      exact pow_le_pow_left₀ (norm_nonneg _) (HD.trans
        (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)) 2)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (sub_pos.mpr hsmall).le)).mp
  rw [norm_toLp_sq_eq_integral]
  exact H.2

lemma identified_cheegerHeat_weighted_norm
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ‖(identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1.toLp
        (fun x => cheegerHeat h t u x*Real.exp (V x))‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq_eq_integral,mul_pow,sq_exp_eq]
  have H := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).2
  simpa only [mul_assoc] using H

lemma identified_cheegerHeat_laplacian_integral_zero
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t A x ∂m) = 0 := by
  have hUt := (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1
  have hAt := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA ht).1
  have hpar := hpar
  have hLap := identified_isLaplacian_of_formGenerator hfinite hID h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  exact hLap.integral_eq_zero hfinite hpar o (integrable_of_memLp_mul_exp hAt hdecay)
    (integrable_of_memLp_mul_exp (hLap.memLp_gradient_mul_exp hfinite hpar hV hUt hAt) hdecay)

lemma identified_cheegerHeat_mass_weighted_generator
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  let C := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)*
      ‖hdecay.toLp (fun x => Real.exp (-V x))‖
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x, cheegerHeat h s A x*radialCutoff o n x ∂m
  have hfn (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (radialCutoffLp hfinite o n)) (cheegerHeat h s A) := by
      funext s; exact integral_radialCutoff_eq_inner hfinite o n _
    rw [he]
    exact (innerSL ℝ (radialCutoffLp hfinite o n)).continuous.comp_continuousOn
      (cheegerHeat_continuousOn hfinite h A)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ C := by
    have hsW := (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs.1).1
    have HH := integral_cutoff_le_weighted hsW hdecay
      (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [abs_of_nonneg (radialCutoff_nonneg o n x)] using radialCutoff_le_one o n x)
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (identified_cheegerHeat_weighted_norm hID hpar hfinite o h A hV hA hs.1).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop (𝓝 0) := by
    have H := integral_radialCutoff_tendsto o
      (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h A hV hA hs).1 hdecay)
    rw [identified_cheegerHeat_laplacian_integral_zero hID hpar hfinite o h hu hV hU hA hdecay hs] at H
    exact H
  have htime : Tendsto (fun n => ∫ s in 0..t, fn n s) atTop (𝓝 0) := by
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Eventually.of_forall (fun n =>
        ((hfn n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc))
      (Eventually.of_forall (fun n => ae_of_all _ fun s hs =>
        hb n s (by rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)))
      (intervalIntegrable_const)
      (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le))
    simpa only [intervalIntegral.integral_zero] using H
  have hFTC (n : ℕ) : (∫ s in 0..t, fn n s) =
      (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (radialCutoffLp hfinite o n)
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := ((cheegerHeat_continuousOn hfinite h A).mono
      (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfinite h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_radialCutoff_eq_inner hfinite o n] using H
  have hsp := (integral_radialCutoff_tendsto o
    (integrable_of_memLp_mul_exp (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hdecay)).sub
      (integral_radialCutoff_tendsto o (integrable_of_memLp_mul_exp hU hdecay))
  rw [show (fun n => ∫ s in 0..t, fn n s) = (fun n =>
    (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m)) from funext hFTC] at htime
  exact sub_eq_zero.mp (tendsto_nhds_unique hsp htime)

lemma identified_cheegerHeat_mass_of_weighted_resolvents
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n, 0 < ts n)
    (hsmall : ∀ n, ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    identified_cheegerResolvent_weighted hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (identified_cheegerResolvent_weighted_norm hID hpar hfinite o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := by
    have H := ((hW n).sub hU).const_smul ((ts n)⁻¹)
    apply MemLp.ae_eq _ H
    filter_upwards [Lp.coeFn_smul ((ts n)⁻¹) (us n-u),Lp.coeFn_sub (us n) u] with x hs hd
    dsimp only [As]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    ring
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have H1 := integral_tendsto_of_weighted_bound hdecay hfinite o hum hU hW hWnorm
  have hWt (n : ℕ) := (identified_cheegerHeat_weighted hID hpar hfinite o h (us n) hV (hW n) ht).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h t (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*t) := by
    exact (identified_cheegerHeat_weighted_norm hID hpar hfinite o h (us n) hV (hW n) ht).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have H2 := integral_tendsto_of_weighted_bound hdecay hfinite o
    ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hum)
    (identified_cheegerHeat_weighted hID hpar hfinite o h u hV hU ht).1 hWt hWtnorm
  have he (n : ℕ) : (∫ x,cheegerHeat h t (us n) x ∂m) = ∫ x,us n x ∂m :=
    identified_cheegerHeat_mass_weighted_generator hID hpar hfinite o h (hus n) hV (hW n) (hAw n) hdecay ht
  simp_rw [Function.comp_def,he] at H2
  exact tendsto_nhds_unique H2 H1

lemma identified_cheegerHeat_mass_localized
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact identified_cheegerHeat_mass_of_weighted_resolvents hID hpar hfinite o h u hV hU hdecay hpos hsmall hlim ht

end WeakHessian

end
end InlinedFile216

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma compact_dual_heat_offset_limit_local
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (u₀ u₁ : Lp ℝ 2 m) {φ₀ φ₁ : X → ℝ} (hφ₀ : MemLp φ₀ 2 m) (hφ₁ : MemLp φ₁ 2 m)
    {T ε η : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hη : 0 < η)
    {A : ℝ → ℝ} (hA : ContinuousAt A 0)
    (H : ∀ δ,δ ∈ Ioo 0 η →
      (∫ x,cheegerHeat h δ u₁ x*φ₁ x ∂m)-
        (∫ x,cheegerHeat h (δ+T) u₀ x*φ₀ x ∂m)+
      T*((∫ x,regularizedEntropy ε (cheegerHeat h (δ+T) u₀ x) ∂m)-
        (∫ x,regularizedEntropy ε (cheegerHeat h δ u₁ x) ∂m)) ≤ A δ) :
    (∫ x,u₁ x*φ₁ x ∂m)-(∫ x,cheegerHeat h T u₀ x*φ₀ x ∂m)+
      T*((∫ x,regularizedEntropy ε (cheegerHeat h T u₀ x) ∂m)-
        (∫ x,regularizedEntropy ε (u₁ x) ∂m)) ≤ A 0 := by
  have h₀ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n+T) u₀) atTop
      (𝓝 (cheegerHeat h T u₀)) := cheegerHeat_tendsto_nonneg hfin h u₀ hT
    (by simpa only [zero_add] using fisherEpsilon_tendsto.add_const T)
    (Eventually.of_forall fun n => add_nonneg (fisherEpsilon_pos n).le hT)
  have h₁ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n) u₁) atTop (𝓝 u₁) := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using
      cheegerHeat_tendsto_nonneg hfin h u₁ (le_refl 0) fisherEpsilon_tendsto
        (Eventually.of_forall fun n => (fisherEpsilon_pos n).le)
  have hE₀ := ((regularizedEntropy_hasFDeriv hε (cheegerHeat h T u₀)).continuousAt).tendsto.comp h₀
  have hE₁ := ((regularizedEntropy_hasFDeriv hε u₁).continuousAt).tendsto.comp h₁
  have hL := ((integral_mul_tendsto_L2 h₁ hφ₁).sub (integral_mul_tendsto_L2 h₀ hφ₀)).add
    ((hE₀.sub hE₁).const_mul T)
  apply le_of_tendsto_of_tendsto hL (hA.tendsto.comp fisherEpsilon_tendsto)
  filter_upwards [fisherEpsilon_tendsto.eventually (gt_mem_nhds hη)] with n hn
  exact H _ ⟨fisherEpsilon_pos n,hn⟩

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BridgeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma heatBridgeError_nonneg (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m)
    (hξ : ∀ᵐ x ∂m,0 ≤ ξ x) {J : X → ℝ} (hJ : ∀ᵐ x ∂m,0 ≤ J x)
    (T : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ heatBridgeError h f ξ J T s := by
  apply integral_nonneg_of_ae
  filter_upwards [cheegerHeat_nonneg h hs ξ hξ,hJ,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hJ hg
  rw [hg]; positivity

lemma heatBridgeError_integrable
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Integrable (fun x => (cheegerHeat h s ξ x*J x)*
      gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m := by
  have hfs : Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  apply (integrable_gamma hfin hfs hfs).bdd_mul
    ((Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable.mul hJm) (c := Cξ*max B 0)
  filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hJb] with x hρ hJ
  change |cheegerHeat h s ξ x*J x| ≤ _
  rw [abs_mul]
  exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ

lemma heatBridgeError_le_energy
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h f ξ J T s ≤ B*heatBridgeEnergy h f ξ T s := by
  rw [← heatBridgeError_const]
  apply integral_mono_ae (heatBridgeError_integrable hfin hID h hf hCξ hξb hJm hJb T hs)
    (heatBridgeError_integrable hfin hID h hf hCξ hξb aestronglyMeasurable_const
      (ae_of_all _ fun _ => le_refl |B|) T hs)
  filter_upwards [cheegerHeat_nonneg h hs.1 ξ hξ0,hJb,
    gamma_self (m := m) (cheegerHeat h (T-s) f)] with x hx hJ hg
  rw [hg]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hJ) hx) (sq_nonneg _)

lemma heatBridgeError_split
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m)
    (h : QuadraticCheegerEnergy m) {f g ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (hJ0 : ∀ᵐ x ∂m,0 ≤ J x) (T c : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h (f+c•g) ξ J T s ≤
      2*heatBridgeError h f ξ J T s+2*c^2*heatBridgeError h g ξ J T s := by
  have hPS (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  let ρ := fun x => cheegerHeat h s ξ x*J x
  have hρm : AEStronglyMeasurable ρ m :=
    (Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable.mul hJm
  have hρb : ∀ᵐ x ∂m,|ρ x| ≤ Cξ*max B 0 := by
    filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hJb] with x hρ hJ
    dsimp [ρ]; rw [abs_mul]
    exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ
  have he (v : Lp ℝ 2 m) : heatBridgeError h v ξ J T s =
      ∫ x,ρ x*(weakGradient m (cheegerHeat h (T-s) v) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (cheegerHeat h (T-s) v)] with x hx
    rw [hx]
  have Hp := weighted_gradient_add_smul hfin hpar (hPS f hf) (hPS g hg) hρm hρb c
  have Hm := weighted_gradient_add_smul hfin hpar (hPS f hf) (hPS g hg) hρm hρb (-c)
  have Hn := heatBridgeError_nonneg h (f+(-c)•g) ξ hξ0 hJ0 T hs.1
  rw [he,map_add,map_smul] at Hn
  rw [he,map_add,map_smul,he,he]
  rw [Hm] at Hn
  rw [Hp]
  nlinarith

lemma heatBridgeError_integral_split
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m)
    (h : QuadraticCheegerEnergy m) {f g ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (hJ0 : ∀ᵐ x ∂m,0 ≤ J x) {T : ℝ} (hT : 0 ≤ T)
    (hDi : ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
      IntervalIntegrable (heatBridgeError h v ξ J T) volume 0 T) (c : ℝ) :
    (∫ s in 0..T,heatBridgeError h (f+c•g) ξ J T s) ≤
      2*(∫ s in 0..T,heatBridgeError h f ξ J T s)+
        2*c^2*(∫ s in 0..T,heatBridgeError h g ξ J T s) := by
  have hfg : Sobolev m (f+c•g : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hg.const_mul c))
    filter_upwards [Lp.coeFn_add f (c•g),Lp.coeFn_smul c g] with x ha hc
    simp only [ha,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := intervalIntegral.integral_mono_on hT (hDi _ hfg)
    (((hDi f hf).const_mul 2).add ((hDi g hg).const_mul (2*c^2)))
    (fun s hs => heatBridgeError_split hfin hID hpar h hf hg hCξ hξb hξ0 hJm hJb hJ0 T c hs)
  rw [intervalIntegral.integral_add ((hDi f hf).const_mul 2)
    ((hDi g hg).const_mul (2*c^2)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at H
  exact H

lemma heatBridgeError_integral_le
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) (hξ0 : ∀ᵐ x ∂m,0 ≤ ξ x)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hB : 0 ≤ B)
    (hJb : ∀ᵐ x ∂m,|J x| ≤ B) {T M : ℝ} (hT : 0 ≤ T)
    (hDi : IntervalIntegrable (heatBridgeError h f ξ J T) volume 0 T)
    (hEM : ∀ s ∈ Icc 0 T,heatBridgeEnergy h f ξ T s ≤ M*heatBridgeEnergy h f ξ T T) :
    (∫ s in 0..T,heatBridgeError h f ξ J T s) ≤ B*T*M*heatBridgeEnergy h f ξ T T := by
  have H := intervalIntegral.integral_mono_on hT hDi
    (intervalIntegrable_const (c := B*M*heatBridgeEnergy h f ξ T T)) (by
      intro s hs
      exact (heatBridgeError_le_energy hfin hID h hf hCξ hξb hξ0 hJm hJb T hs).trans
        ((mul_le_mul_of_nonneg_left (hEM s hs) hB).trans_eq (by ring)))
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_left_comm,mul_assoc] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedHeatDen_one_le (K a c CG : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    1 ≤ localizedHeatDen K a c CG T := by
  dsimp [localizedHeatDen,localizedHeatM]
  exact le_add_of_nonneg_right (by positivity)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedHeatFactor_pos (K a c CG : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 < localizedHeatFactor K a c CG T := by
  dsimp [localizedHeatFactor,localizedHeatDen,localizedHeatM]
  positivity

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.localized_heat_certificate {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let ν := exponentialMeasure m (fun x => a*F x)
    let R := localizedHeatError h ξ G K a c CG T
    let b := localizedHeatFactor K a c CG T
    (∀ f : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) →
      b*(∫ x,ξ x*(weakGradient ν (cheegerHeat h T f) x)^2 ∂ν) ≤
        (∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν)+R f) ∧
    (∀ f g : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) → Sobolev ν (g : X → ℝ) →
      ∀ t : ℝ,R (f+t•g) ≤ 2*R f+2*t^2*R g) ∧
    (∀ f : Lp ℝ 2 ν,Sobolev ν (f : X → ℝ) →
      0 ≤ R f ∧ R f ≤ 2*a*(CG+|c|)*T*localizedHeatM K a CG T*
        (∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν)) := by
  dsimp only
  let ν := exponentialMeasure m (fun x => a*F x)
  let J := fun x => max (G x-c) 0
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (exponentialMeasure_comparable (m := m) hVB).1 (exponentialMeasure_comparable (m := m) hVB).2
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hJm : AEStronglyMeasurable J ν := ((hGc.sub continuous_const).max continuous_const).aestronglyMeasurable
  have hJb : ∀ᵐ x ∂ν,|J x| ≤ CG+|c| := ae_of_all _ fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [(abs_le.mp (hGb x)).2,neg_le_abs c]
    · positivity
  have hJ0 : ∀ᵐ x ∂ν,0 ≤ J x := ae_of_all _ fun _ => le_max_right _ _
  have H := fun f hf => hHess.localized_heat_gradient hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (f := f) (ξ := ξ) hf hCξ hξb hξ0 c hT
  have hDi (f : Lp ℝ 2 ν) (hf : Sobolev ν (f : X → ℝ)) :
      IntervalIntegrable (heatBridgeError h f ξ J T) volume 0 T := (H f hf).2.1
  have hDn := localizedHeatDen_one_le K a c CG hT
  have hDp : 0 < localizedHeatDen K a c CG T := zero_lt_one.trans_le hDn
  have hθ : 0 ≤ 2*a/localizedHeatDen K a c CG T := by positivity
  have hθb : 2*a/localizedHeatDen K a c CG T ≤ 2*a := by
    apply (div_le_iff₀ hDp).mpr
    nlinarith
  have hend (f : Lp ℝ 2 ν) : heatBridgeEnergy h f ξ T T =
      ∫ x,cheegerHeat h T ξ x*(weakGradient ν f x)^2 ∂ν := by
    rw [heatBridgeEnergy_end]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) f] with x hx
    rw [hx]
  refine ⟨?_,?_,?_⟩
  · intro f hf
    have Hf := (H f hf).2.2
    have hzero : heatBridgeEnergy h f ξ T 0 =
        ∫ x,ξ x*(weakGradient ν (cheegerHeat h T f) x)^2 ∂ν := by
      rw [heatBridgeEnergy_zero]
      apply integral_congr_ae
      filter_upwards [gamma_self (m := ν) (cheegerHeat h T f)] with x hx
      rw [hx]
    rw [hzero,hend] at Hf
    exact Hf
  · intro f g hf hg t
    have HH := mul_le_mul_of_nonneg_left
      (heatBridgeError_integral_split hnfin hID hpar h hf hg hCξ hξb hξ0 hJm hJb hJ0 hT hDi t) hθ
    dsimp [localizedHeatError]
    convert HH using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  · intro f hf
    have hIn : 0 ≤ ∫ s in 0..T,heatBridgeError h f ξ J T s :=
      intervalIntegral.integral_nonneg hT (fun s hs => heatBridgeError_nonneg h f ξ hξ0 hJ0 T hs.1)
    have hIb := heatBridgeError_integral_le hnfin hID h hf hCξ hξb hξ0 hJm
      (by positivity : 0 ≤ CG+|c|) hJb hT (hDi f hf)
      (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).2)
    refine ⟨mul_nonneg hθ hIn,?_⟩
    rw [hend] at hIb
    change (2*a/localizedHeatDen K a c CG T)*(∫ s in 0..T,heatBridgeError h f ξ J T s) ≤ _
    exact (mul_le_mul_of_nonneg_right hθb hIn).trans
      ((mul_le_mul_of_nonneg_left hIb (by positivity : 0 ≤ 2*a)).trans_eq (by dsimp [localizedHeatM]; ring))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_OneSidedBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

lemma exists_oneSidedKernel {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ : ℝ → ℝ,HasCompactSupport κ ∧ ContDiff ℝ 1 κ ∧
      (∀ r,0 ≤ κ r) ∧ (∫ r,κ r) = 1 ∧ Function.support κ ⊆ Icc 0 δ := by
  let f : ContDiffBump (δ/2) := ⟨δ/4,δ/2,by linarith,by linarith⟩
  refine ⟨f.normed volume,f.hasCompactSupport_normed,f.contDiff_normed,
    f.nonneg_normed,f.integral_normed,?_⟩
  rw [f.support_normed_eq]
  intro r hr
  change dist r (δ/2) < δ/2 at hr
  rw [Real.dist_eq,abs_lt] at hr
  constructor <;> linarith [hr.1,hr.2]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma timeAverageLaw_terminal_ball {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : ∀ᵐ s ∂ν,s ∈ Icc 0 δ) {r D : ℝ} (_ : 0 ≤ D)
    (o : X) (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) o ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D) :
    ∀ᵐ x ∂timeAverageLaw π ν 1,dist x o ≤ r+δ*D := by
  apply (ae_map_iff (continuous_timeAverageEval 1).measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  have Hδ : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,z.1 ∈ Icc 0 δ :=
    ae_of_ae_map measurable_fst.aemeasurable (by simpa only [Measure.map_fst_prod,measure_univ,one_smul] using hδ)
  have Hγ : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,IsGeodesic z.2 ∧
      dist (z.2 timeOne) o ≤ r ∧ dist (z.2 timeZero) (z.2 timeOne) ≤ D := by
    exact ae_of_ae_map (μ := ν.prod π) (f := Prod.snd) measurable_snd.aemeasurable
      (by simpa only [Measure.map_snd_prod,measure_univ,one_smul] using hgeo.and (hs.and hl))
  filter_upwards [Hδ,Hγ] with z hz hγ
  change dist (z.2 (clampTime (1-z.1))) o ≤ _
  have ht : |(clampTime (1-z.1):ℝ)-(timeOne:ℝ)| ≤ δ := by
    have ha := (clampTime (1-z.1)).property
    change 0 ≤ max 0 (min 1 (1-z.1)) ∧ max 0 (min 1 (1-z.1)) ≤ 1 at ha
    change |max 0 (min 1 (1-z.1))-1| ≤ δ
    rw [abs_of_nonpos (by linarith : max 0 (min 1 (1-z.1))-1 ≤ 0)]
    have hh : 1-z.1 ≤ max 0 (min 1 (1-z.1)) := by
      rw [min_eq_right (by linarith [hz.1])]
      exact le_max_right _ _
    linarith [hz.2]
  have hd := mul_le_mul ht hγ.2.2 dist_nonneg (le_trans (abs_nonneg _) ht)
  have H := dist_triangle (z.2 (clampTime (1-z.1))) (z.2 timeOne) o
  rw [hγ.1] at H
  linarith [hγ.2.1]

lemma kernelMeasure_ae_support {κ : ℝ → ℝ} (hc : Continuous κ) {S : Set ℝ}
    (hs : Function.support κ ⊆ S) : ∀ᵐ r ∂kernelMeasure κ,r ∈ S := by
  apply (ae_withDensity_iff hc.measurable.ennreal_ofReal).mpr
  exact ae_of_all _ fun r hr => hs (by
    intro hz
    exact hr (by simp only [hz,ENNReal.ofReal_zero]))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_OneSidedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_zero_of_nonnegative_support {κ : ℝ → ℝ}
    (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r) (hi : Integrable κ)
    (hm : ∫ r, κ r = 1) (hs : ∀ r, r < 0 → κ r = 0)
    (u : Time → Lp ℝ 2 m) : smoothDensity κ u 0 = u timeZero := by
  rw [smoothDensity_eq_average hc hn,integral_kernelMeasure hc hn]
  have he : (fun r : ℝ => κ r • u (clampTime (0-r))) = fun r => κ r • u timeZero := by
    funext r
    by_cases hr : r < 0
    · simp only [hs r hr,zero_smul]
    · have hz : clampTime (0-r) = timeZero := by
        apply Subtype.ext
        simp only [clampTime,timeZero]
        apply max_eq_left
        exact min_le_of_right_le (by linarith)
      rw [hz]
  rw [he]
  calc
    _ = (∫ r, κ r) • u timeZero :=
      ((1 : ℝ →L[ℝ] ℝ).smulRight (u timeZero)).integral_comp_comm hi
    _ = u timeZero := by rw [hm, one_smul]

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile217
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_supported {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hd⟩ := hrcd.1.exists_decay_weight hN hfull hfin o
  have hW : LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |a*dist x o-a*dist y o| ≤ |a| * dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)
  have huW := memLp_exp_dist_of_support u ha.le o hR
  have hd' : MemLp (fun x => Real.exp (-(a*dist x o))) 2 ν := by
    simpa only [neg_mul] using hd.of_measure_le_smul (by simp : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞) hν
  refine ⟨integrable_of_memLp_mul_exp
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u hW huW ht).1 hd', ?_⟩
  exact identified_cheegerHeat_mass_localized hID hnpar hnfin o h u hW huW hd' ht

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_nonneg {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hu : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hi : Integrable u (exponentialMeasure m V)) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal)
    (exponentialMeasure_comparable (m := m) hBV).2
  have hsub := cheegerHeat_submass hnfin o h u hu hi ht
  refine ⟨hsub.1,le_antisymm hsub.2 ?_⟩
  have hχ (n : ℕ) : ∀ᵐ x ∂ν, |radialCutoff o n x| ≤ (1:ℝ) := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let us (n : ℕ) : Lp ℝ 2 ν := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (hχ n) u
  have he (n : ℕ) : us n =ᵐ[ν] fun x => u x*radialCutoff o n x := boundedMulLp_ae _ _ u
  have hs (n : ℕ) : ∀ᵐ x ∂ν, (n:ℝ)+1 ≤ dist x o → us n x = 0 := by
    filter_upwards [he n] with x hx hdist
    rw [hx]
    have hz : radialCutoff o n x = 0 := by
      apply max_eq_left
      have H : 1 ≤ dist x o/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by simpa using hdist)
      linarith
    rw [hz,mul_zero]
  have hle (n : ℕ) : ∀ᵐ x ∂ν, us n x ≤ u x := by
    filter_upwards [he n,hu] with x hx hpos
    rw [hx]
    exact mul_le_of_le_one_right hpos (radialCutoff_le_one o n x)
  have hmass (n : ℕ) := hrcd.weighted_heat_mass_supported hN hfull hfin o hBV h (us n) (hs n) ht
  have hbound (n : ℕ) : (∫ x,u x*radialCutoff o n x ∂ν) ≤ ∫ x,cheegerHeat h t u x ∂ν := by
    rw [← integral_congr_ae (he n),← (hmass n).2]
    exact integral_mono_ae (hmass n).1 hsub.1 (cheegerHeat_order h ht (us n) u (hle n))
  exact le_of_tendsto (integral_radialCutoff_tendsto o hi) (Eventually.of_forall hbound)

end WeakHessian

end
end InlinedFile217

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalizedActionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma localizedHeatM_one_le {K a CG T : ℝ} (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    1 ≤ localizedHeatM K a CG T := Real.one_le_exp (by positivity)

lemma reciprocal_factor_bound {k t M : ℝ} (ht : 0 ≤ t) (hM : 1 ≤ M) :
    (1+2*max (-k) 0*t*M)/(1+2*max k 0*t/M) ≤
      1-2*k*t+2*|k| *t*(M-1)+4*k^2*t^2 := by
  have hMp : 0 < M := zero_lt_one.trans_le hM
  rcases le_total k 0 with hk | hk
  · rw [max_eq_left (by linarith : 0 ≤ -k), max_eq_right hk,abs_of_nonpos hk]
    simp only [mul_zero,zero_mul,zero_div,add_zero,div_one]
    nlinarith [sq_nonneg (k*t)]
  · rw [max_eq_right (by linarith : -k ≤ 0),max_eq_left hk,abs_of_nonneg hk]
    simp only [mul_zero,zero_mul,add_zero]
    let x := 2*k*t/M
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hrec : 1/(1+x) ≤ 1-x+x^2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1+x)).mpr
      nlinarith [mul_nonneg (sq_nonneg x) hx]
    have hxle : x ≤ 2*k*t := by
      dsimp [x]; apply (div_le_iff₀ hMp).mpr
      nlinarith [mul_nonneg hk ht]
    have hlin : -x ≤ -2*k*t+2*k*t*(M-1) := by
      dsimp [x]
      rw [← neg_div]
      apply (div_le_iff₀ hMp).mpr
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*k*t) (sq_nonneg (M-1))]
    have hsq : x^2 ≤ (2*k*t)^2 := (sq_le_sq₀ hx (by positivity)).mpr hxle
    change 1/(1+x) ≤ _
    exact hrec.trans (by nlinarith only [hlin,hsq])

lemma localizedHeatFactor_reciprocal_bound {K a c CG t U : ℝ}
    (ha : 0 ≤ a) (hCG : 0 ≤ CG) (ht : 0 ≤ t) (htU : t ≤ U) :
    1/localizedHeatFactor K a c CG t ≤
      1-2*(K-a*c)*t+2*|K-a*c| *U*(localizedHeatM K a CG U-1)+4*(K-a*c)^2*U^2 := by
  have hM := localizedHeatM_one_le (K := K) ha hCG ht
  have hMU : localizedHeatM K a CG t ≤ localizedHeatM K a CG U := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htU (by positivity)
  have hU : 0 ≤ U := ht.trans htU
  have H := reciprocal_factor_bound (k := K-a*c) ht hM
  have he : 1/localizedHeatFactor K a c CG t =
      (1+2*max (-(K-a*c)) 0*t*localizedHeatM K a CG t)/
        (1+2*max (K-a*c) 0*t/localizedHeatM K a CG t) := by
    dsimp [localizedHeatFactor,localizedHeatDen]
    rw [one_div_div]
  rw [he]
  apply H.trans
  have hprod := mul_le_mul htU (sub_le_sub_right hMU 1) (sub_nonneg.mpr hM) hU
  have hsq := (sq_le_sq₀ ht hU).mpr htU
  have h1 := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2*|K-a*c|)
  have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4*(K-a*c)^2)
  nlinarith only [h1,h2]

lemma localizedHeatFactor_continuousOn (K a c CG : ℝ) :
    ContinuousOn (localizedHeatFactor K a c CG) (Ici 0) := by
  unfold localizedHeatFactor
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    apply continuous_const.add
    exact (by fun_prop : Continuous (fun t : ℝ => 2*max (K-a*c) 0*t)).div
      (show Continuous (fun t : ℝ => localizedHeatM K a CG t) from by unfold localizedHeatM; fun_prop) (fun t => Real.exp_ne_zero _)
  · change ContinuousOn (fun t : ℝ => 1+2*max (-(K-a*c)) 0*t*Real.exp (2*(|K|+a*CG)*t)) (Ici 0)
    fun_prop
  · intro t ht
    exact (zero_lt_one.trans_le (localizedHeatDen_one_le K a c CG ht)).ne'

lemma localized_action_integral_bound {K a c CG δ T E : ℝ}
    (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    (∫ s in (0:ℝ)..1,E/localizedHeatFactor K a c CG (backwardsHeatTime δ T s)/2) ≤
      E/2*(1-2*(K-a*c)*δ-(K-a*c)*T+
        2*|K-a*c| *(δ+T)*(localizedHeatM K a CG (δ+T)-1)+4*(K-a*c)^2*(δ+T)^2) := by
  let U := δ+T
  let A := 2*|K-a*c| *U*(localizedHeatM K a CG U-1)+4*(K-a*c)^2*U^2
  have hθn (s : ℝ) : 0 ≤ backwardsHeatTime δ T s := by
    simp only [backwardsHeatTime]; positivity
  have hθc : Continuous (backwardsHeatTime δ T) := by change Continuous (fun s : ℝ => δ+T*max (1-s) 0); fun_prop
  have hbc := (localizedHeatFactor_continuousOn K a c CG).comp_continuous hθc hθn
  have hic : Continuous (fun s => E/localizedHeatFactor K a c CG (backwardsHeatTime δ T s)/2) :=
    (continuous_const.div hbc (fun s => (localizedHeatFactor_pos K a c CG (hθn s)).ne')).div_const 2
  have hB : Continuous (fun s : ℝ => E/2*(1-2*(K-a*c)*(δ+T*(1-s))+A)) := by fun_prop
  have H := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hic.intervalIntegrable (μ := volume) 0 1) (hB.intervalIntegrable (μ := volume) 0 1) (fun s hs => by
      have hθ : backwardsHeatTime δ T s = δ+T*(1-s) := by
        simp only [backwardsHeatTime]; rw [max_eq_left (by linarith [hs.2])]
      have htU : backwardsHeatTime δ T s ≤ U := by rw [hθ]; dsimp [U]; nlinarith [hs.1]
      have H := mul_le_mul_of_nonneg_left
        (localizedHeatFactor_reciprocal_bound (K := K) (c := c) ha hCG (hθn s) htU) (by positivity : 0 ≤ E/2)
      rw [hθ] at H ⊢
      convert H using 1 <;> first | rfl | ((try dsimp only [A]); ring))
  have he (s : ℝ) : E/2*(1-2*(K-a*c)*(δ+T*(1-s))+A) =
      E/2*(1-2*(K-a*c)*δ-2*(K-a*c)*T+A)+E*(K-a*c)*T*s := by ring
  simp_rw [he] at H
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id] at H
  simp only [sub_zero,one_pow,zero_pow (by norm_num : (2:ℕ) ≠ 0),smul_eq_mul,one_mul] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ((try dsimp only [A,U]); ring)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_SmoothedPlanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma density_zero_of_ae_law {u : Lp ℝ 2 m} (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {P : X → Prop} (hP : ∀ᵐ x ∂densityMeasure m u,P x) :
    ∀ᵐ x ∂m,¬P x → u x = 0 := by
  have H := (ae_withDensity_iff (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)).mp hP
  filter_upwards [H,hun] with x hx hn hnp
  have he : ENNReal.ofReal (u x) = 0 := by
    by_contra hz
    exact hnp (hx hz)
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp he) hn

lemma timeAverageLaw_ae_of_tracks {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {P : X → Prop}
    (hPm : MeasurableSet {x | P x}) (hP : ∀ᵐ γ ∂π,∀ t : Time,P (γ t)) (s : ℝ) :
    ∀ᵐ x ∂timeAverageLaw π ν s,P x := by
  apply (ae_map_iff (continuous_timeAverageEval s).measurable.aemeasurable hPm).mpr
  have H : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,∀ t : Time,P (z.2 t) := by
    exact ae_of_ae_map (μ := ν.prod π) (p := fun γ => ∀ t : Time,P (γ t))
      measurable_snd.aemeasurable (by simpa only [Measure.map_snd_prod,measure_univ,one_smul] using hP)
  filter_upwards [H] with z hz
  exact hz (clampTime (s-z.1))

lemma BoundedTracks.timeAverageLaw_bounded {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ o : X,∃ R : ℝ,0 < R ∧ ∀ s : ℝ,∀ᵐ x ∂timeAverageLaw π ν s,dist x o ≤ R := by
  obtain ⟨o,R,hR,hb⟩ := hb
  exact ⟨o,R,hR,fun s => timeAverageLaw_ae_of_tracks ν (measurableSet_le (by fun_prop) measurable_const) hb s⟩

lemma timeAverageLaw_integrable_dist {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) (o : X) :
    Integrable (fun x => dist x o) (timeAverageLaw π ν s) := by
  let := isProbabilityMeasure_timeAverageLaw π ν s
  obtain ⟨a,R,hR,hb⟩ := hb.timeAverageLaw_bounded ν
  apply Integrable.of_bound (by fun_prop) (R+dist a o)
  filter_upwards [hb s] with x hx
  rw [Real.norm_of_nonneg dist_nonneg]
  exact (dist_triangle x a o).trans (by linarith)

lemma smoothDensity_integrable_dist
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hc : Continuous κ) (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) (o : X) :
    Integrable (fun x => smoothDensity κ u s x*dist x o) m := by
  let : IsProbabilityMeasure π := hπ.1
  let := kernelMeasure_probability hi hn hm
  obtain ⟨hsn,_,_,_,hsl,_⟩ := hπ.smoothDensity_properties hB hu hun hlaw hnorm hc hi hn hm s
  have H := timeAverageLaw_integrable_dist hb (kernelMeasure κ) s o
  rw [← hsl] at H
  rw [densityMeasure,integrable_withDensity_iff_integrable_smul'
    (Lp.stronglyMeasurable _ |>.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at H
  exact H.congr (by
    filter_upwards [hsn] with x hx
    simp only [ENNReal.toReal_ofReal hx,smul_eq_mul])

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_WeightedEntropyCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma integrable_mul_of_exp_weights {u W : X → ℝ}
    (hu : MemLp (fun x => u x*Real.exp (W x)) 2 m)
    (hW : MemLp (fun x => W x*Real.exp (-W x)) 2 m) :
    Integrable (fun x => u x*W x) m := by
  apply (hu.integrable_mul hW).congr
  exact ae_of_all _ fun x => by
    change (u x*Real.exp (W x))*(W x*Real.exp (-W x)) = u x*W x
    rw [show (u x*Real.exp (W x))*(W x*Real.exp (-W x)) =
      (u x*W x)*(Real.exp (W x)*Real.exp (-W x)) by ring,
      ← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

lemma RCD.weighted_heat_entropy_tails {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0) :
    ∃ a : ℝ,0 < a ∧ Integrable (fun x => Real.exp (-(a*dist x o))) (exponentialMeasure m V) ∧
      Integrable (fun x => u x*(a*dist x o)) (exponentialMeasure m V) ∧
      ∀ t : ℝ,0 ≤ t → Integrable (fun x => cheegerHeat h t u x*(a*dist x o)) (exponentialMeasure m V) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hi,h2,hD,hh,hhi⟩ := hrcd.1.exists_strong_entropy_confinement hN hfull hfin o
  have hCt : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞ := by simp
  have hi' : Integrable (fun x => Real.exp (-(a*dist x o))) ν := by
    apply memLp_one_iff_integrable.mp
    exact (memLp_one_iff_integrable.mpr hi).of_measure_le_smul hCt hν
  have hD' : MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 ν :=
    hD.of_measure_le_smul hCt hν
  have huW := memLp_exp_dist_of_support u ha.le o hR
  refine ⟨a,ha,hi',integrable_mul_of_exp_weights huW hD',?_⟩
  intro t ht
  exact integrable_mul_of_exp_weights
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u (lipschitz_mul_dist o a) huW ht).1 hD'

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalizedPlanDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_localized_plan_dual {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤
      (B : ℝ≥0∞) • exponentialMeasure m (fun x => a*F x))
    {u : Time → Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hu : StronglyMeasurable u)
    (hun : ∀ t,∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u t x)
    (hlaw : ∀ t,densityMeasure (exponentialMeasure m (fun x => a*F x)) (u t) =
      π.map (fun γ => γ t)) (hnorm : ∀ t,‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r,0 ≤ κ r) (hm : ∫ r,κ r = 1)
    {d β r R T U Q c : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 (exponentialMeasure m (fun x => a*F x)))
    (hsupp : ∀ s : ℝ,∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),r ≤ dist x o → smoothDensity κ u s x = 0)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T < U)
    (hQ : ∀ s : ℝ,‖smoothDensity κ u s‖*‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖ ≤ Q)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    let ν := exponentialMeasure m (fun x => a*F x)
    (∫ x,smoothDensity κ u 1 x*boundedHopfMap f (q+1) x ∂ν)-
      (∫ x,cheegerHeat h T (smoothDensity κ u 0) x*boundedHopfMap f q x ∂ν)+
      T*((∫ x,reducedEntropy (cheegerHeat h T (smoothDensity κ u 0) x) ∂ν)-
        (∫ x,reducedEntropy (smoothDensity κ u 1 x) ∂ν)) ≤
      planKineticCost π/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip f q) Q d β R r := by
  dsimp only
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsProbabilityMeasure π := hπ.1
  have hpν := hπ.of_measure_le_smul hmν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure hmν hνm
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hi : Integrable κ := hc.continuous.integrable_of_hasCompactSupport hκ
  have hprop := fun s => hpν.smoothDensity_properties hB hu hun hlaw hnorm hc.continuous hi hn hm s
  let := kernelMeasure_probability hi hn hm
  obtain ⟨b,Rb,hRb,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hsupport : ∀ᵐ x ∂ν,Rb+1 ≤ dist x b → smoothDensity κ u 0 x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨cd,hcd,hV,hUV,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h
    (smoothDensity κ u 0) hsupport
  have hu1V : Integrable (fun x => smoothDensity κ u 1 x*(cd*dist x b)) ν := by
    convert (smoothDensity_integrable_dist hpν hb hB hu hun hlaw hnorm hc.continuous hi hn hm 1 b).mul_const cd using 1
    all_goals try with_reducible_and_instances rfl
    funext x; ring
  have hPm := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h (smoothDensity κ u 0)
    (hprop 0).1 (hprop 0).2.2.1 hT).2.trans (hprop 0).2.2.2.1
  have hPn := cheegerHeat_nonneg h hT (smoothDensity κ u 0) (hprop 0).1
  apply entropy_dual_of_regularized (cheegerHeat h T (smoothDensity κ u 0)) (smoothDensity κ u 1)
    (integrable_of_integral_eq_one hPm) (hprop 1).2.2.1 (hPm.trans (hprop 1).2.2.2.1.symm)
    hPn (hprop 1).1 (hPV T hT) hu1V hV (D := compactHopfDualBound hnfin o f hf hq/2)
  intro ε hε
  let Eerror := curvatureTailBound K a c CG U (hopfUniformLip f q) Q d β R r
  let A := fun δ : ℝ => planKineticCost π/2*(1-2*(K-a*c)*δ-(K-a*c)*T+
    2*|K-a*c| *(δ+T)*(localizedHeatM K a CG (δ+T)-1)+4*(K-a*c)^2*(δ+T)^2)+Eerror+
      ε*compactHopfDualBound hnfin o f hf hq/2
  have hAc : ContinuousAt A 0 := by dsimp [A,localizedHeatM]; fun_prop
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have H := compact_dual_heat_offset_limit_local hnfin h (smoothDensity κ u 0) (smoothDensity κ u 1)
    (boundedHopfMap_memLp_compact hnfin f o hf hq)
    (boundedHopfMap_memLp_compact hnfin f o hf (by linarith : 0 < q+1)) hT hε
    (sub_pos.mpr hTU) hAc (by
      intro δ hδ
      have hθU (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : backwardsHeatTime δ T s ≤ U := by
        dsimp [backwardsHeatTime]
        rw [max_eq_left (by linarith [hs.2])]
        nlinarith [hδ.2,hs.1]
      have hθn (s : ℝ) : 0 ≤ backwardsHeatTime δ T s := (backwardsHeatTime_pos hδ.1 hT s).le
      have hcert := fun s => hHess.localized_heat_certificate hN hrcd hfull hfin o hF hFb hGb hGc ha h
        B.coe_nonneg (hprop s).2.1 (hprop s).1 c (hθn s)
      have HD := cheegerHeat_plan_entropy_dual_error hnfin o hID hnpar h hpν hb hgeo hB hu hun hlaw hnorm
        hκ hc hn hm hδ.1 hT hq f hf (localizedHeatFactor_continuousOn K a c CG)
        (fun t ht => localizedHeatFactor_pos K a c CG ht)
        (R := fun s => localizedHeatError h (smoothDensity κ u s) G K a c CG (backwardsHeatTime δ T s))
        (fun s _ => (hcert s).1) (fun s _ => (hcert s).2.1) (by
          intro s hs v hv
          have HB := (hcert s).2.2 v hv
          have hEn : 0 ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient ν v x)^2 ∂ν := by
            apply integral_nonneg_of_ae
            filter_upwards [cheegerHeat_nonneg h (hθn s) _ (hprop s).1] with x hx
            positivity
          have hMt : localizedHeatM K a CG (backwardsHeatTime δ T s) ≤ localizedHeatM K a CG U := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (hθU s hs) (by positivity)
          have hscale : 4*a*(CG+|c|)*(backwardsHeatTime δ T s)*localizedHeatM K a CG (backwardsHeatTime δ T s) ≤ 1 := by
            apply le_trans _ hsmall
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hθU s hs) (by positivity)) hMt
              (Real.exp_pos _).le (mul_nonneg (by positivity) (hT.trans hTU.le))
          have Hscale := mul_le_mul_of_nonneg_right hscale hEn
          nlinarith only [HB.2,Hscale]) (by
          intro s hs v hv hDb
          exact hHess.localized_heatError_tail_bound hN hrcd hfull hfin o hF hFb hGb hGc ha h
            hv (hopfUniformLip_nonneg f hq) hDb (hprop s).2.2.1 B.coe_nonneg (hprop s).2.1 (hprop s).1
            hd hdβ hdecay (hsupp s) hlocal (hθn s) (hθU s hs) (hQ s)) ε hε
      have HA := localized_action_integral_bound (K := K) (c := c) ha.le hCG hδ.1.le hT (planKineticCost_nonneg π)
      exact HD.trans (by change _ ≤ A δ; dsimp only [A,Eerror]; linarith))
  simpa only [A,Eerror,localizedActionBound,mul_zero,sub_zero,zero_add,mul_div_assoc] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanComparisonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_injective_nonneg {u v : Lp ℝ 2 m}
    (hu : ∀ᵐ x ∂m,0 ≤ u x) (hv : ∀ᵐ x ∂m,0 ≤ v x)
    (he : densityMeasure m u = densityMeasure m v) : u = v := by
  have H := (withDensity_eq_iff_of_sigmaFinite
    (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal.aemeasurable)
    (Lp.stronglyMeasurable v |>.measurable.ennreal_ofReal.aemeasurable)).mp he
  apply Lp.ext
  filter_upwards [H,hu,hv] with x hx hu hv
  have H := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalizedPlanLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_localized_plan_law_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u₀ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hu₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ)
    (hlaw₀ : densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀ = π.map (fun γ => γ timeZero))
    {B : ℝ≥0} (hB : ∀ t : Time,π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {r D S : ℝ} (hD : 0 ≤ D) (x₁ : X)
    (hs : ∀ᵐ γ ∂π,dist (γ timeOne) x₁ ≤ r)
    (hl : ∀ᵐ γ ∂π,dist (γ timeZero) (γ timeOne) ≤ D)
    (htracks : ∀ᵐ γ ∂π,∀ t : Time,dist (γ t) o < S)
    {d β R T U c δ : ℝ} (hd : 0 ≤ d) (hdβ : d ≤ β)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    (hT : 0 ≤ T) (hTU : T < U) (hδ : 0 < δ)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
    ∃ μ : ProbabilityMeasure X, FiniteEntropy m (μ:Measure X) ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧
      (∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r+δ*D) ∧
      ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X))-
        (∫ x,boundedHopfMap f q x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ≤
      planKineticCost π/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip f q)
          (((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
          entropyReal (exponentialMeasure m (fun x => a*F x))
            (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hCF : 0 ≤ CF := (abs_nonneg (F o)).trans (hFb o)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVB
  rw [abs_of_pos ha] at hmν hνm
  let E : ℝ≥0 := (Real.exp (a*CF)).toNNReal
  have hE : (E:ℝ) = Real.exp (a*CF) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hnfin := hfin.of_le_smul (C := E) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsProbabilityMeasure π := hπ.1
  have hpν := hπ.of_measure_le_smul hmν
  have hB' (t : Time) : π.map (fun γ => γ t) ≤ ((B*E:ℝ≥0):ℝ≥0∞) • ν := by
    apply (hB t).trans
    simpa only [ENNReal.coe_mul,smul_smul,E,ν,ENNReal.ofReal] using smul_le_smul_left (B:ℝ≥0∞) hmν
  obtain ⟨u,hu,hun,_hub,hui,hum,hul,hunorm⟩ := hpν.exists_L2_density_curve_bound hnfin hb hB'
  have hu0 : u timeZero = u₀ := densityMeasure_injective_nonneg (hun _) hu₀ ((hul _).trans hlaw₀.symm)
  obtain ⟨κ,hκ,hc,hn,hm,hsκ⟩ := exists_oneSidedKernel hδ
  have hi : Integrable κ := hc.continuous.integrable_of_hasCompactSupport hκ
  let := kernelMeasure_probability hi hn hm
  have hzκ : ∀ t,t < 0 → κ t = 0 := fun t ht => by
    by_contra hc
    exact (not_le_of_gt ht) (hsκ hc).1
  have hs0 : smoothDensity κ u 0 = u₀ :=
    (smoothDensity_zero_of_nonnegative_support hc.continuous hn hi hm hzκ u).trans hu0
  have hprop := fun s => hpν.smoothDensity_properties hB' hu hun hul hunorm hc.continuous hi hn hm s
  let := isProbabilityMeasure_timeAverageLaw π (kernelMeasure κ) 1
  let μ : ProbabilityMeasure X := ⟨timeAverageLaw π (kernelMeasure κ) 1,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hμ : (μ:Measure X) = densityMeasure ν (smoothDensity κ u 1) := (hprop 1).2.2.2.2.1.symm
  have hμB : (μ:Measure X) ≤ (B : ℝ≥0∞) • m := hπ.timeAverageLaw_le hB _ 1
  obtain ⟨b,Rb,hRb,hbR⟩ := hb.timeAverageLaw_bounded (kernelMeasure κ)
  have hμE : FiniteEntropy m (μ:Measure X) :=
    finiteEntropy_of_bounded_supported hfin μ b ⟨Rb,hRb.le⟩ (ae_iff.mp (hbR 1)) ENNReal.coe_ne_top hμB
  have h0support : ∀ᵐ x ∂ν,Rb+1 ≤ dist x b → u₀ x = 0 := by
    have H := density_zero_of_ae_law (hprop 0).1 (by rw [(hprop 0).2.2.2.2.1]; exact hbR 0)
    rw [hs0] at H
    filter_upwards [H] with x hx hd
    exact hx (by linarith)
  obtain ⟨cd,_hcd,he,_,hPV⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin b hVB h u₀ h0support
  have hu1V : Integrable (fun x => smoothDensity κ u 1 x*(cd*dist x b)) ν := by
    convert (smoothDensity_integrable_dist hpν hb hB' hu hun hul hunorm hc.continuous hi hn hm 1 b).mul_const cd using 1
    all_goals try with_reducible_and_instances rfl
    funext x; ring
  have hPm : ∫ x,cheegerHeat h T u₀ x ∂ν = 1 := by
    have H := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h u₀ hu₀
      (by simpa only [← hu0] using hui timeZero) hT).2
    rw [H,← hu0]; exact hum timeZero
  have hPn := cheegerHeat_nonneg h hT u₀ hu₀
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u₀) hPn (integrable_of_integral_eq_one hPm) hPm
  let μP : ProbabilityMeasure X := ⟨densityMeasure ν (cheegerHeat h T u₀),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hEc := entropyReal_eq_reducedDensity (smoothDensity κ u 1) (hprop 1).1 (hprop 1).2.2.1
    (integrable_reducedEntropy (Lp.memLp _) (hprop 1).1 hu1V he) μ hμ
  have hEP := entropyReal_eq_reducedDensity (cheegerHeat h T u₀) hPn (integrable_of_integral_eq_one hPm)
    (integrable_reducedEntropy (Lp.memLp _) hPn (hPV T hT) he) μP rfl
  have hdν := hdecay.of_measure_le_smul ENNReal.coe_ne_top hνm
  have hsup (s : ℝ) : ∀ᵐ x ∂ν,S ≤ dist x o → smoothDensity κ u s x = 0 := by
    have H := density_zero_of_ae_law (hprop s).1 (by
      rw [(hprop s).2.2.2.2.1]
      exact timeAverageLaw_ae_of_tracks (kernelMeasure κ) (measurableSet_lt (show Measurable (fun x : X => dist x o) from by fun_prop) measurable_const) htracks s)
    filter_upwards [H] with x hx hs
    exact hx (not_lt.mpr hs)
  have hQ (s : ℝ) : ‖smoothDensity κ u s‖*‖hdν.toLp (fun x => Real.exp (-d*dist x o))‖ ≤
      ((B:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF) := by
    have H := norm_product_of_compression (B := B) (E := E) (by rw [hE]; exact Real.one_le_exp (by positivity)) hνm
      ((hprop s).2.2.2.2.2) hdecay hdν
    rw [hE,← Real.exp_nat_mul] at H
    convert H using 1 <;> first | rfl | (congr 1; ring_nf)
  refine ⟨μ,hμE,hμB,timeAverageLaw_terminal_ball _ (kernelMeasure_ae_support hc.continuous hsκ) hD x₁ hgeo hs hl,?_⟩
  intro f hf q hq
  have HD := hHess.rcd_localized_plan_dual hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hπ hb hgeo hB' hu hun hul hunorm hκ hc hn hm hd hdβ hdν hsup hlocal hT hTU hQ hsmall f hf hq
  rw [hs0] at HD
  change entropyReal ν (densityMeasure ν (cheegerHeat h T u₀)) = _ at hEP
  rw [hEc,hEP]
  rw [hμ,integral_densityMeasure ν _ (hprop 1).1,integral_densityMeasure ν _ hPn]
  linarith only [HD]
end WeakHessian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law_oai.{u_1} := @OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law_oai.{u_1}
