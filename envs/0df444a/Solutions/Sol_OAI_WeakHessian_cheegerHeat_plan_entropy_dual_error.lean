-- Prove2me | solution 1 for OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:16:17.009883+00:00
-- url     : https://prove2.me/submissions/c4af4bd6-f007-41ca-91e7-80a01ec84efc

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

lemma cheegerHeat_add (h : QuadraticCheegerEnergy m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cheegerHeat h (t+s) = cheegerHeat h t * cheegerHeat h s := realHeat_add m _ ht hs

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatInverseSymbol
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
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma heatInverseSymbol_continuous (t : ℝ) : Continuous (heatInverseSymbol t) := by
  have hc := expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  simp only [Polynomial.eval_X] at hc
  exact continuous_const.mul (hc.comp (continuous_id.div_const t))

lemma heatInverseSymbol_mul {t : ℝ} (ht : 0 < t) (s : ℝ) :
    s * heatInverseSymbol t s = heatSymbol t s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_mul, heatSymbol_nonpos ht le_rfl]
  · rw [heatInverseSymbol, heatSymbol, ite_eq_right ht.ne', inv_div]
    field_simp

lemma heatSymbol_maps_range {t : ℝ} (ht : 0 < t) (s : ℝ) :
    heatSymbol t s = s*heatInverseSymbol t s := (heatInverseSymbol_mul ht s).symm

lemma resolventHeat_eq_resolvent_mul {R : H →L[ℂ] H} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) :
    resolventHeat R t = R*cfc (heatInverseSymbol t) R := by
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  calc
    resolventHeat R t = cfc (fun s : ℝ => s*heatInverseSymbol t s) R :=
      cfc_congr fun s _ => heatSymbol_maps_range ht s
    _ = cfc (fun s : ℝ => s) R*cfc (heatInverseSymbol t) R :=
      cfc_mul _ _ _ continuous_id.continuousOn (heatInverseSymbol_continuous t).continuousOn
    _ = _ := by rw [hid]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatGeneratorOperator
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

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_3_r9d9f65_1 : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
lemma realHeat_mem_range {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) : realHeat m R t u ∈ R.toLinearMap.range := by
  refine ⟨realCfc m R (heatInverseSymbol t) u, ?_⟩
  apply ofRealLp_injective m
  change ofRealLp m (R (realCfc m R (heatInverseSymbol t) u)) = _
  rw [← complexify_ofReal m R, ofReal_realCfc, ofReal_realHeat,
    resolventHeat_eq_resolvent_mul (complexify_positive m hR) ht]
  rfl

end WeakHessianFunctional
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_hasFormGenerator {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    ∃ A, hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u) A := by
  obtain ⟨v,hv⟩ := realHeat_mem_range m hQ.resolvent_positive ht u
  change hQ.resolvent v = realHeat m hQ.resolventLinear t u at hv
  refine ⟨hQ.resolvent v-v, ?_⟩
  rw [← hv]
  exact hQ.isFormGenerator_resolvent v

end WeakHessianFunctional

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

lemma IsTestPlan.integrable_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : Integrable f m) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  obtain ⟨C,hC⟩ := hπ.2.1
  exact ((hf.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable
    (continuous_eval_const t).measurable.aemeasurable

lemma IsTestPlan.integrable_eval_local {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R)))
    (t : Time) : Integrable (fun γ => f (γ t)) π := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  exact hplan.integrable_eval (hf o R hR) t

lemma IsTestPlan.continuous_integral_eval_local (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R))) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact hplan.continuous_integral_eval (hf o R hR)

lemma LocallyL2.integrable_eval (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocallyL2 m f) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  apply hπ.integrable_eval_local hb _ t
  intro o R hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact (hf o R hR).integrable (by norm_num)

lemma LocallyL2.integrable_sq_eval {f : X → ℝ} (hf : LocallyL2 m f)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (t : Time) :
    Integrable (fun γ => (f (γ t))^2) π :=
  hπ.integrable_eval_local hb (fun o R hR => (hf o R hR).integrable_sq) t

lemma LocallyL2.continuous_integral_sq_eval (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocallyL2 m f) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    Continuous (fun t : Time => ∫ γ, (f (γ t))^2 ∂π) :=
  hπ.continuous_integral_eval_local hfin hb (fun o R hR => (hf o R hR).integrable_sq)

lemma LocallyL2.integrable_sq_prod_eval {D : X → ℝ} (hD : LocallyL2 m D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2)
      (π.prod (volume.restrict (Icc (0:ℝ) 1))) := by
  let : IsProbabilityMeasure π := hπ.1
  have hm := (hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
  rw [lintegral_prod _ hm.ennreal_ofReal]
  exact hπ.lintegral_square_eval_lt_top hb hD

lemma IsTestPlan.continuous_local_gradient_energy (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} (hf : LocalSobolev m f) :
    Continuous (fun s : ℝ => ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π) :=
  ((weakGradient_isMinimal hf.2).1.1.continuous_integral_sq_eval hfin hπ hb).comp continuous_clampTime

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma IsLocalWeakUpperGradient.geodesic_young_local
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
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
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) :=
    (hD.1.integrable_sq_prod_eval hπ hb).mono_measure hprod
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

end WeakHessian

noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young_time_local
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
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
  have hDI : Integrable (fun z : Curve X × ℝ => (D (evalReal z.1 z.2))^2) (π.prod ν) :=
    (hD.1.integrable_sq_prod_eval hπ hb).mono_measure hprod
  have hLI := hb.integrable_length_sq.comp_fst ν
  have H := hD.geodesic_young_local hf hπ hb hgeo t ht
  calc
    _ ≤ _ := H
    _ = _ := by
      rw [integral_div,integral_add hDI hLI,integral_prod_symm _ hDI,integral_prod _ hLI]
      simp only [ν,integral_const,Measure.real,Measure.restrict_apply_univ,
        Real.volume_Icc,sub_zero,smul_eq_mul,ENNReal.toReal_ofReal ht.le]
      rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.le]

end WeakHessian

end
end
end InlinedFile1

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

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

lemma regularizedEntropy_zero (a : ℝ) : regularizedEntropy a 0 = 0 := by
  simp [regularizedEntropy]
lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedLog a) ((max a (x+a))⁻¹) x := by
  simpa only [regularizedLog,Function.comp_def,mul_one] using!
    ((truncatedLog_hasDeriv ha (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub_const (Real.log a)
lemma regularizedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedLog a) x = (max a (x+a))⁻¹ := (regularizedLog_hasDeriv ha x).deriv
lemma regularizedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedLog a) x| ≤ a⁻¹ := by
  rw [regularizedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a (x+a))))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma regularizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedEntropy a) (regularizedLog a x) x := by
  have hc := (regularizedLog_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

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
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiffLipschitz
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
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.comp_contDiff_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) :
    Sobolev m (φ ∘ f) := by
  have hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ (L:ℝ) :=
    ae_of_all _ (fun x => norm_deriv_le_of_lipschitz hLip)
  have hmeas : AEStronglyMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf.1.aemeasurable).abs.aestronglyMeasurable
  apply Sobolev.of_upperGradient hfinite (hLip.comp_memLp hzero hf.1)
    ((weakGradient_isMinimal hf.2.1.2).1.comp_contDiff hf.1.aemeasurable hφ hB)
  simpa only [mul_comm] using memLp_mul_bounded hf.2.2 hmeas (by simpa only [abs_abs] using hB)

end WeakHessian

end
end InlinedFile0

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

lemma regularizedLog_weighted_gamma (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u f : X → ℝ}
    (hu : Sobolev m u) (hf : Sobolev m f)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    (fun x => (u x+ε)*gamma m f (regularizedLog ε ∘ u) x) =ᵐ[m] gamma m f u := by
  have hr := hu.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
  filter_upwards [gamma_comp_contDiff hfin hpar hu.2.1 hf.2.1
    (regularizedLog_contDiff hε) hr.2.1.1
    (ae_of_all _ fun x => regularizedLog_deriv_bound hε (u x)),
    gamma_comm (m := m) f (regularizedLog ε ∘ u),gamma_comm (m := m) u f,hun]
    with x hc h1 h2 hn
  rw [h1,hc,regularizedLog_deriv hε,max_eq_right (by linarith : ε ≤ u x+ε),h2]
  have hnz : u x+ε ≠ 0 := ne_of_gt (by linarith)
  field_simp

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

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weighted_gradient_smul (ρ : X → ℝ) (f : Lp ℝ 2 m) (c : ℝ) :
    (∫ x, ρ x*(weakGradient m (c•f : Lp ℝ 2 m) x)^2 ∂m) =
      c^2*(∫ x, ρ x*(weakGradient m f x)^2 ∂m) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hc : (c•f : Lp ℝ 2 m) =ᵐ[m] (fun x => c*f x) := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa only [Pi.smul_apply,smul_eq_mul] using hx
  filter_upwards [weakGradient_congr_ae hc,weakGradient_const_mul (m := m) c (f : X → ℝ)]
    with x h1 h2
  rw [h1,h2,mul_pow,sq_abs]
  ring

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LocalizedFisher
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
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma logarithmic_shift_error_absorb
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) {R : Lp ℝ 2 m → ℝ}
    (hv : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪v,f⟫_ℝ ≤ A+(∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m)+R f)
    (t : ℝ) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ}
    (hR : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      R (f+t•r) ≤ E+t^2*(∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m)) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    2*⟪v+t•L,f⟫_ℝ ≤ A+E-2*t*⟪v+t•L,r⟫_ℝ+
      ∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m := by
  dsimp only
  let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
  have hre : (r : X → ℝ) =ᵐ[m] regularizedLog ε ∘ (u : X → ℝ) :=
    (regularizedLog_memLp hε u).coeFn_toLp
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae hre).mpr
    (hu.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  have hρm : AEStronglyMeasurable (fun x => u x+ε) m :=
    (Lp.memLp u).aestronglyMeasurable.add_const ε
  have hρb : ∀ᵐ x ∂m, |u x+ε| ≤ B+ε := by
    filter_upwards [hub] with x hx
    exact (abs_add_le _ _).trans (by rw [abs_of_pos hε]; linarith)
  have hcross (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      (∫ x, (u x+ε)*gamma m f r x ∂m) = -⟪L,f⟫_ℝ := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, gamma m f u x ∂m := by
        apply integral_congr_ae
        filter_upwards [gamma_congr_ae (Filter.EventuallyEq.rfl : (f : X → ℝ) =ᵐ[m] f) hre,
          regularizedLog_weighted_gamma hfin hpar hu.1 hf hun hε] with x h1 h2
        rw [h1]; exact h2
      _ = ∫ x, gamma m u f x ∂m := integral_congr_ae (gamma_comm _ _)
      _ = _ := by
        rw [hu.2.2 f hf]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [RCLike.inner_apply,conj_trivial]; ring
  have hrq : (∫ x, (u x+ε)*(weakGradient m r x)^2 ∂m) = -⟪L,r⟫_ℝ := by
    rw [← hcross r hr]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (r : X → ℝ)] with x hx
    rw [hx]
  have hfr : Sobolev m (f+t•r : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hr.const_mul t))
    filter_upwards [Lp.coeFn_add f (t•r),Lp.coeFn_smul t r] with x ha hs
    simp only [ha,hs,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := hv (f+t•r) hfr
  have HR := hR
  change R (f+t•r) ≤ E+t^2*(∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m) at HR
  rw [hrq] at HR
  rw [weighted_gradient_add_smul hfin hpar hf hr hρm hρb t,hcross f hf,hrq] at H
  simp only [inner_add_right,inner_smul_right,inner_add_left,real_inner_smul_left] at H ⊢
  nlinarith

lemma logarithmic_shift_split_absorb
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) {R : Lp ℝ 2 m → ℝ}
    (hv : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪v,f⟫_ℝ ≤ A+(∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m)+R f)
    (t : ℝ) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ}
    (hRf : R f ≤ E)
    (hsplit : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      R (f+t•r) ≤ 2*R f+2*t^2*R r)
    (hrelative : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      2*R r ≤ ∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    2*⟪v+t•L,f⟫_ℝ ≤ A+2*E-2*t*⟪v+t•L,r⟫_ℝ+
      ∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m := by
  apply logarithmic_shift_error_absorb hfin hpar hu hun hub hε hv t hf
  dsimp only at hsplit hrelative ⊢
  nlinarith [mul_le_mul_of_nonneg_left hrelative (sq_nonneg t)]

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

omit [SigmaFinite m] in
lemma timeAverageLaw_integral
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) {f : X → ℝ} (hf : Integrable f m) :
    (∫ x, f x ∂timeAverageLaw π ν s) =
      ∫ r, (∫ x, u (clampTime (s-r)) x*f x ∂m) ∂ν := by
  let : IsProbabilityMeasure π := hπ.1
  have hle := hπ.timeAverageLaw_le hB ν s
  have hfi : Integrable f (timeAverageLaw π ν s) :=
    (hf.smul_measure ENNReal.coe_ne_top).mono_measure hle
  have hprod : Integrable (fun z : ℝ × Curve X => f (evalReal z.2 (s-z.1))) (ν.prod π) :=
    (integrable_map_measure hfi.1 (continuous_timeAverageEval s).measurable.aemeasurable).mp hfi
  rw [timeAverageLaw,integral_map (continuous_timeAverageEval s).measurable.aemeasurable hfi.1,
    integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [← integral_densityMeasure _ _ (hun _),hlaw]
  exact (integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
    (hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))).symm

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

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma locallyIntegrable_clampedDensity {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ)) :
    LocallyIntegrable (fun t => u (clampTime t)) := by
  rw [locallyIntegrable_iff]
  intro S hS
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  apply Integrable.of_bound (hu.comp_measurable continuous_clampTime.measurable).aestronglyMeasurable
    ((B : ℝ)+1)
  filter_upwards [] with r
  change ‖u (clampTime r)‖ ≤ (B : ℝ)+1
  have hb := hB (clampTime r)
  have hn := norm_nonneg (u (clampTime r))
  have hB0 := B.coe_nonneg
  nlinarith [sq_nonneg (‖u (clampTime r)‖-1)]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_hasDerivAt {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    {B : ℝ≥0} (hB : ∀ t, ‖u t‖^2 ≤ (B : ℝ)) (s : ℝ) :
    HasDerivAt (smoothDensity κ u) (smoothDensity (deriv κ) u s) s :=
  hκ.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hc
    (locallyIntegrable_clampedDensity hu hB) s

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile130
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => cheegerHeat h s u) (cheegerHeat h t A) t := by
  have hc := cheegerHeat_continuousOn hfin h A
  have hat := (hc t ht.le).continuousAt (Ici_mem_nhds ht)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := (hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) t ht) hat).add_const u
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [cheegerHeat_integral_generator hfin h hu hs.le, sub_add_cancel]
end WeakHessian

end
end InlinedFile130

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatPositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile131
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_positive (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t) :
    ∃ A : Lp ℝ 2 m, (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A ∧
      HasDerivAt (fun s => cheegerHeat h s u) A t := by
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨B,hB⟩ := Q.heat_hasFormGenerator m (half_pos ht) u
  change Q.IsFormGenerator (cheegerHeat h (t/2) u) B at hB
  let A := cheegerHeat h (t/2) B
  have hg := Q.formGenerator_heat m hB (t/2)
  have he : cheegerHeat h (t/2) (cheegerHeat h (t/2) u) = cheegerHeat h t u := by
    have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (half_pos ht).le (half_pos ht).le)
    simpa only [add_halves,mul_apply_eq_comp] using H.symm
  change Q.IsFormGenerator (cheegerHeat h (t/2) (cheegerHeat h (t/2) u)) A at hg
  refine ⟨A,he ▸ hg,?_⟩
  have HD := cheegerHeat_deriv_at_generator hfin h hB (half_pos ht)
  have hc := (hasDerivAt_id t).sub_const (t/2)
  have H := HD.scomp_of_eq t hc (by rw [id_eq, sub_half] : t/2 = id t-t/2)
  simp only [Function.comp_def,one_smul,id_eq] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
    (cheegerHeat_add h (show 0 ≤ s-t/2 by linarith) (half_pos ht).le)
  simpa only [sub_add_cancel,mul_apply_eq_comp] using H
end WeakHessian

end
end InlinedFile131

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatDiagonal
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
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma cheegerHeat_tendsto_joint
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {u : ι → Lp ℝ 2 m}
    {T : ℝ} {v : Lp ℝ 2 m} (hT : 0 < T)
    (hθ : Tendsto θ l (𝓝 T)) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun z => cheegerHeat h (θ z) (u z)) l (𝓝 (cheegerHeat h T v)) := by
  have hc : ContinuousAt (fun s => cheegerHeat h s v) T :=
    ((cheegerHeat_continuousOn hfin h v) T hT.le).continuousAt (Ici_mem_nhds hT)
  have hz : ∀ᶠ z in l, 0 ≤ θ z :=
    (hθ.eventually (eventually_gt_nhds hT)).mono fun _ hz => hz.le
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ᶠ z in l, dist (cheegerHeat h (θ z) (u z)) (cheegerHeat h T v) ≤
      dist (u z) v + dist (cheegerHeat h (θ z) v) (cheegerHeat h T v) := by
    filter_upwards [hz] with z hz
    have h1 := dist_triangle (cheegerHeat h (θ z) (u z))
      (cheegerHeat h (θ z) v) (cheegerHeat h T v)
    have h2 := cheegerHeat_contractive h hz (u z) v
    exact h1.trans (add_le_add h2 le_rfl)
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hb
  simpa only [zero_add,Function.comp_def] using
    (tendsto_iff_dist_tendsto_zero.mp hu).add
      (tendsto_iff_dist_tendsto_zero.mp (hc.tendsto.comp hθ))

lemma cheegerHeat_diagonal_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s := by
  obtain ⟨L,hL,hLD⟩ := cheegerHeat_deriv_at_positive hfin h (u s) hpos
  refine ⟨L,hL,?_⟩
  have ha : HasDerivAt (fun z => cheegerHeat h (θ z) (u z-u s))
      (cheegerHeat h (θ s) v) s := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have H := cheegerHeat_tendsto_joint hfin h hpos
      (hθ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hu.tendsto_slope
    apply H.congr'
    exact Eventually.of_forall fun z => by
      simp only [slope_def_module,sub_self,map_zero,sub_zero,map_smul]
  have hb : HasDerivAt (fun z => cheegerHeat h (θ z) (u s)) (τ • L) s :=
    hLD.scomp s hθ
  apply (ha.add hb).congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    simp only [Pi.add_apply,map_sub,sub_add_cancel]

lemma cheegerHeat_diagonal_entropy_hasDerivAt
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Lp ℝ 2 m,
      (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h (θ s) (u s)) L ∧
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z))
        (cheegerHeat h (θ s) v + τ • L) s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m)
        ⟪cheegerHeat h (θ s) v + τ • L,
          (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).toLp
            (fun x => regularizedLog ε (cheegerHeat h (θ s) (u s) x))⟫_ℝ s := by
  obtain ⟨L,hL,hD⟩ := cheegerHeat_diagonal_hasDerivAt hfin h hθ hu hpos
  refine ⟨L,hL,hD,?_⟩
  have H := (regularizedEntropy_hasFDeriv hε (cheegerHeat h (θ s) (u s))).comp_hasDerivAt s hD
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  exact real_inner_comm _ _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_ScaledPlanYoung
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile220
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.geodesic_young_time_scaled
    {f D : X → ℝ} (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ} (hC : 0 < C) (t : Time) (ht : 0 < t.val) :
    (∫ γ,f (γ t)-f (γ timeZero) ∂π) ≤
      C/2*(∫ s in 0..t.val,∫ γ,(D (evalReal γ s))^2 ∂π)+
        t.val/(2*C)*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) := by
  have H := (hD.const_mul (-C)).geodesic_young_time_local (hf.const_mul (-C)) hπ hb hgeo t ht
  have hleft : (∫ γ,(-C)*f (γ timeZero)-(-C)*f (γ t) ∂π) =
      C*(∫ γ,f (γ t)-f (γ timeZero) ∂π) := by
    rw [← integral_const_mul]
    congr 1; funext γ; ring
  have hs (s : ℝ) : (∫ γ,(|-C| *D (evalReal γ s))^2 ∂π) =
      C^2*(∫ γ,(D (evalReal γ s))^2 ∂π) := by
    simp only [abs_neg,abs_of_pos hC,mul_pow,integral_const_mul]
  rw [hleft] at H
  simp_rw [hs] at H
  rw [intervalIntegral.integral_const_mul] at H
  have H' := div_le_div_of_nonneg_right H hC.le
  rw [mul_div_cancel_left₀ _ hC.ne'] at H'
  calc
    _ ≤ _ := H'
    _ = _ := by field_simp [hC.ne']
end WeakHessian

end
end InlinedFile220

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanHamiltonJacobiAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile223
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma IsGeodesic.restrictCurve {γ : Curve X} (hγ : IsGeodesic γ) (a b : Time) :
    IsGeodesic (restrictCurve a b γ) := by
  intro s t
  change dist (γ (affineTime a b s)) (γ (affineTime a b t)) =
    |(s : ℝ)-(t : ℝ)| *dist (γ (affineTime a b timeZero)) (γ (affineTime a b timeOne))
  rw [affineTime_zero,affineTime_one,hγ (affineTime a b s) (affineTime a b t),hγ a b]
  have he : (affineTime a b s : ℝ)-(affineTime a b t : ℝ) =
      ((b : ℝ)-(a : ℝ))*((s : ℝ)-(t : ℝ)) := by dsimp [affineTime]; ring
  rw [he,abs_mul,abs_sub_comm (b : ℝ) (a : ℝ)]
  ring

end WeakHessian

end
end InlinedFile223

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

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma planGradientEnergy_nonneg (m : Measure X) (π : Measure (Curve X)) (f : X → ℝ) (t : Time) :
    0 ≤ planGradientEnergy m π f t := integral_nonneg fun _ => sq_nonneg _
omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma planKineticCost_nonneg (π : Measure (Curve X)) : 0 ≤ planKineticCost π :=
  integral_nonneg fun _ => sq_nonneg _

lemma IsTestPlan.plan_increment_bound (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {f : X → ℝ} (hf : LocalSobolev m f)
    (a b : Time) (hab : (a : ℝ) ≤ b) {M : ℝ}
    (hM : ∀ t : Time, (a : ℝ) ≤ t → (t : ℝ) ≤ b → planGradientEnergy m π f t ≤ M) :
    planMoment π f b-planMoment π f a ≤ ((b : ℝ)-a)/2*(M+planKineticCost π) := by
  by_cases he : a = b
  · subst b; simp
  have hab' : (a : ℝ) < b := lt_of_le_of_ne hab (fun h => he (Subtype.ext h))
  let : IsProbabilityMeasure π := hπ.1
  let c := (b : ℝ)-a
  have hc : 0 < c := sub_pos.mpr hab'
  let π' := π.map (WeakHessian.restrictCurve a b)
  have hp' : IsTestPlan m π' := hπ.restrictCurve a b hab'
  have hb' : BoundedTracks π' := hb.restrictCurve a b
  have hg' : ∀ᵐ γ ∂π', IsGeodesic γ :=
    continuous_ae_map_of_ae (continuous_restrictCurve a b) (hgeo.mono fun _ h => h.restrictCurve a b)
  have hD := (weakGradient_isMinimal hf.2).1
  have H := hD.geodesic_young_time_scaled hf.1.aemeasurable hp' hb' hg' hc timeOne (by norm_num [timeOne])
  have hleft : (∫ γ, f (γ timeOne)-f (γ timeZero) ∂π') =
      planMoment π f b-planMoment π f a := by
    rw [integral_sub (hf.1.integrable_eval hfin hp' hb' timeOne) (hf.1.integrable_eval hfin hp' hb' timeZero)]
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hf.1.integrable_eval hfin hp' hb' timeOne).1,
      integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hf.1.integrable_eval hfin hp' hb' timeZero).1]
    simp only [restrictCurve_one,restrictCurve_zero,planMoment]
  have hcost : (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π') = c^2*planKineticCost π := by
    have hm : AEStronglyMeasurable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π' :=
      (by fun_prop : Continuous (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2)).aestronglyMeasurable
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable hm,planKineticCost,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgeo] with γ hγ
    rw [restrictCurve_zero,restrictCurve_one,hγ a b,abs_of_nonpos (sub_nonpos.mpr hab),mul_pow]
    dsimp only [c]
    ring
  have henergy : (∫ s in (0:ℝ)..1, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π') ≤ M := by
    have hci := hp'.continuous_local_gradient_energy hfin hb' hf
    have HH := intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1 by norm_num)
      (hci.intervalIntegrable 0 1) (intervalIntegrable_const (c := M)) ?_
    · simpa using HH
    intro s hs
    change (∫ γ, (weakGradient m f (γ (clampTime s)))^2 ∂π.map (WeakHessian.restrictCurve a b)) ≤ M
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hD.1.integrable_sq_eval hp' hb' (clampTime s)).1]
    change planGradientEnergy m π f (affineTime a b (clampTime s)) ≤ M
    apply hM
    · rw [coe_affineTime]
      have ht := (clampTime s).property.1
      nlinarith
    · rw [coe_affineTime]
      have ht := (clampTime s).property.2
      nlinarith
  rw [hleft,hcost] at H
  change planMoment π f b-planMoment π f a ≤ c/2*(M+planKineticCost π)
  change planMoment π f b-planMoment π f a ≤
    c/2*(∫ s in (0:ℝ)..1, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π')+
      1/(2*c)*(c^2*planKineticCost π) at H
  calc
    _ ≤ _ := H
    _ ≤ c/2*M+1/(2*c)*(c^2*planKineticCost π) := by gcongr
    _ = _ := by field_simp

lemma lipschitzWith_clampTime : LipschitzWith 1 clampTime := by
  have h := (LipschitzWith.const (0:ℝ)).max ((LipschitzWith.const (1:ℝ)).min LipschitzWith.id)
  have he : max (0:ℝ≥0) (max 0 1) = 1 := by norm_num
  rw [he] at h
  exact h.subtype_mk _

lemma monotone_clampTime_coe : Monotone (fun t : ℝ => (clampTime t : ℝ)) :=
  monotone_const.max (monotone_const.min monotone_id)

lemma IsTestPlan.uniform_plan_increment (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {f : X → ℝ} (hf : LocalSobolev m f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a : ℝ, ∀ h : ℝ, 0 < h → h < δ →
      planMoment π f (clampTime (a+h))-planMoment π f (clampTime a) ≤
        h/2*(planGradientEnergy m π f (clampTime a)+ε+planKineticCost π) := by
  have hD := (weakGradient_isMinimal hf.2).1
  have hc : Continuous (planGradientEnergy m π f) :=
    hD.1.continuous_integral_sq_eval hfin hπ hb
  obtain ⟨δ,hδ,hUC⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ,hδ,?_⟩
  intro a h hh hhd
  have hab : (clampTime a : ℝ) ≤ clampTime (a+h) := monotone_clampTime_coe (by linarith)
  have hd : (clampTime (a+h) : ℝ)-(clampTime a : ℝ) ≤ h := by
    have H := lipschitzWith_clampTime.dist_le_mul (a+h) a
    simpa only [one_mul,NNReal.coe_one,Subtype.dist_eq,Real.dist_eq,add_sub_cancel_left,
      abs_of_nonneg hh.le,abs_of_nonneg (sub_nonneg.mpr hab)] using H
  have H := hπ.plan_increment_bound hfin hb hgeo hf (clampTime a) (clampTime (a+h)) hab
    (M := planGradientEnergy m π f (clampTime a)+ε) (by
      intro t hta htb
      have ht : dist t (clampTime a) < δ := by
        rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hta)]
        linarith
      have hu := hUC ht
      rw [Real.dist_eq,abs_lt] at hu
      linarith)
  apply H.trans
  gcongr
  exact add_nonneg (add_nonneg (planGradientEnergy_nonneg _ _ _ _) hε.le) (planKineticCost_nonneg _)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanAction
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
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma integrable_shifted_time_function {J : Time → ℝ} (hJ : Continuous J)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun r => J (clampTime (s-r))) ν := by
  obtain ⟨C,hC⟩ := (isCompact_range hJ.norm).bddAbove
  apply Integrable.of_bound
    ((hJ.comp (continuous_clampTime.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) C
  exact ae_of_all _ fun r => hC ⟨clampTime (s-r),rfl⟩

lemma IsTestPlan.average_density_action (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {s : ℝ} {v : Lp ℝ 2 m}
    (hv : HasDerivAt (fun z => ∫ r, u (clampTime (z-r)) ∂ν) v s) :
    FormActionBound m ((∫ r, u (clampTime (s-r)) ∂ν) : Lp ℝ 2 m) v (planKineticCost π) := by
  let w := fun z => ∫ r, u (clampTime (z-r)) ∂ν
  have hw (z : ℝ) := hπ.exists_timeAverageDensity hB hu hun hlaw hnorm ν z
  intro f hf
  have hJ : Continuous (planMoment π (f : X → ℝ)) :=
    hπ.continuous_integral_eval_local hfin hb (by
      intro o R hR
      let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
        simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
      exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).integrable (by norm_num))
  have hH : Continuous (planGradientEnergy m π (f : X → ℝ)) :=
    (weakGradient_isMinimal hf.2.1.2).1.1.continuous_integral_sq_eval hfin hπ hb
  have hJi (z : ℝ) := integrable_shifted_time_function hJ ν z
  have hHi (z : ℝ) := integrable_shifted_time_function hH ν z
  have hJlaw (t : Time) : planMoment π (f : X → ℝ) t = ⟪f,u t⟫_ℝ := by
    rw [← integral_densityMeasure_L2 _ _ (hun t),hlaw t]
    exact (integral_map (continuous_eval_const t).measurable.aemeasurable
      ((Lp.memLp f).aestronglyMeasurable.mono_ac
        (Measure.absolutelyContinuous_of_le_smul (hB t)))).symm
  have hpair (z : ℝ) : ⟪f,w z⟫_ℝ = ∫ r, planMoment π (f : X → ℝ) (clampTime (z-r)) ∂ν := by
    simp_rw [hJlaw]
    exact ((innerSL ℝ f).integral_comp_comm (integrable_shiftedDensity hu hnorm ν z)).symm
  have henergy : (∫ x, w s x*(weakGradient m f x)^2 ∂m) =
      ∫ r, planGradientEnergy m π (f : X → ℝ) (clampTime (s-r)) ∂ν := by
    rw [← integral_densityMeasure _ _ (hw s).1,(hw s).2.2.2.2.1,
      timeAverageLaw_integral hπ hB hun hlaw ν s hf.2.2.integrable_sq]
    apply integral_congr_ae
    filter_upwards [] with r
    rw [← integral_densityMeasure _ _ (hun _),hlaw]
    exact integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
      (hf.2.2.integrable_sq.1.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))
  have hderiv : HasDerivAt (fun z => ⟪f,w z⟫_ℝ) ⟪f,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s f).inner ℝ hv
  have hlimit : Tendsto (fun h : ℝ => (⟪f,w (s+h)⟫_ℝ-⟪f,w s⟫_ℝ)/h)
      (𝓝[>] 0) (𝓝 ⟪f,v⟫_ℝ) := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hderiv.tendsto_slope_zero_right
  have hεbound (ε : ℝ) (hε : 0 < ε) :
      ⟪f,v⟫_ℝ ≤ ((∫ r, planGradientEnergy m π (f : X → ℝ) (clampTime (s-r)) ∂ν)+ε+planKineticCost π)/2 := by
    obtain ⟨δ,hδ,H⟩ := hπ.uniform_plan_increment hfin hb hgeo hf.2.1 hε
    apply le_of_tendsto hlimit
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hδ
    filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hhd
    change 0 < h at hh
    rw [div_le_iff₀ hh,hpair,hpair,← integral_sub (hJi (s+h)) (hJi s)]
    have H' := integral_mono_ae ((hJi (s+h)).sub (hJi s))
      ((((hHi s).add (integrable_const ε)).add (integrable_const (planKineticCost π))).const_mul (h/2))
      (ae_of_all _ fun r => by
        have hr := H (s-r) h hh hhd
        simpa only [show s-r+h = s+h-r by ring,Pi.sub_apply,Pi.add_apply] using hr)
    simp only [integral_const_mul, Pi.add_apply, Pi.sub_apply] at H'
    have hI1 : Integrable (fun r => planGradientEnergy m π (f : X → ℝ)
        (clampTime (s-r))+ε) ν := (hHi s).add (integrable_const ε)
    rw [integral_add hI1 (integrable_const (planKineticCost π)),
      integral_add (hHi s) (integrable_const ε)] at H'
    simp only [integral_const,probReal_univ,one_smul] at H'
    nlinarith [H']
  rw [real_inner_comm f v,henergy]
  apply le_of_forall_pos_le_add
  intro ε hε
  have H := hεbound ε hε
  linarith

lemma IsTestPlan.smoothDensity_action (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) :
    FormActionBound m (smoothDensity κ u s) (smoothDensity (deriv κ) u s) (planKineticCost π) := by
  let := kernelMeasure_probability (hc.continuous.integrable_of_hasCompactSupport hκ) hn hm
  have he : smoothDensity κ u = fun z => ∫ r, u (clampTime (z-r)) ∂kernelMeasure κ := by
    funext z
    exact smoothDensity_eq_average hc.continuous hn u z
  have hd := smoothDensity_hasDerivAt hκ hc hu hnorm s
  rw [he] at hd ⊢
  exact hπ.average_density_action hfin hb hgeo hB hu hun hlaw hnorm (kernelMeasure κ) hd

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

lemma backwardsHeatTime_hasDerivAt (δ T : ℝ) {s : ℝ} (hs : s < 1) :
    HasDerivAt (backwardsHeatTime δ T) (-T) s := by
  have he : backwardsHeatTime δ T =ᶠ[𝓝 s] fun z => δ+T*(1-z) := by
    filter_upwards [eventually_lt_nhds hs] with z hz
    simp only [backwardsHeatTime,max_eq_left (by linarith : 0 ≤ 1-z)]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (((hasDerivAt_id s).const_sub 1).const_mul T).const_add δ using 1 <;> simp

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PerturbedAction
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
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma FormActionBound.symmetric_contraction_error
    {P : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hP : P.toLinearMap.IsSymmetric)
    (hPS : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) → Sobolev m (P f : X → ℝ))
    {ρ ρ' : X → ℝ} {c : ℝ} (hc : 0 < c) {R : Lp ℝ 2 m → ℝ}
    (hgrad : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      c*(∫ x,ρ x*(weakGradient m (P f) x)^2 ∂m) ≤
        (∫ x,ρ' x*(weakGradient m f x)^2 ∂m)+R f)
    {v : Lp ℝ 2 m} {A : ℝ} (hv : FormActionBound m ρ v A) :
    ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪P v,f⟫_ℝ ≤ A/c+(∫ x,ρ' x*(weakGradient m f x)^2 ∂m)+R f := by
  intro f hf
  have hcs : Sobolev m (c•P f : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr ((hPS f hf).const_mul c)
    filter_upwards [Lp.coeFn_smul c (P f)] with x hx
    simpa only [Pi.smul_apply,smul_eq_mul] using hx
  have H := hv (c•P f) hcs
  have hsym : ⟪P v,f⟫_ℝ = ⟪v,P f⟫_ℝ := hP v f
  rw [weighted_gradient_smul,inner_smul_right,← hsym] at H
  have Hg := mul_le_mul_of_nonneg_left (hgrad f hf) hc.le
  have H' : 2*⟪P v,f⟫_ℝ-(∫ x,ρ' x*(weakGradient m f x)^2 ∂m)-R f ≤ A/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  linarith

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_gradient_le_regularized {ρ : X → ℝ}
    (hρ : AEStronglyMeasurable ρ m) {B : ℝ} (hb : ∀ᵐ x ∂m,|ρ x| ≤ B)
    {ε : ℝ} (hε : 0 ≤ ε) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) :
    (∫ x,ρ x*(weakGradient m f x)^2 ∂m) ≤
      ∫ x,(ρ x+ε)*(weakGradient m f x)^2 ∂m := by
  have hi := hf.2.2.integrable_sq.bdd_mul hρ (by simpa only [Real.norm_eq_abs] using hb)
  simp_rw [add_mul]
  rw [integral_add hi (hf.2.2.integrable_sq.const_mul ε),integral_const_mul]
  exact le_add_of_nonneg_right (mul_nonneg hε (integral_nonneg fun _ => sq_nonneg _))

omit [SigmaFinite m] in
lemma cheegerHeat_diagonal_entropy_test_error
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂m,|u s x| ≤ B)
    (hun : ∀ᵐ x ∂m,0 ≤ u s x) {c : ℝ} (hc : 0 < c)
    {R : Lp ℝ 2 m → ℝ}
    (hgrad : ∀ f : Lp ℝ 2 m,Sobolev m (f : X → ℝ) →
      c*(∫ x,u s x*(weakGradient m (cheegerHeat h (θ s) f) x)^2 ∂m) ≤
        (∫ x,cheegerHeat h (θ s) (u s) x*(weakGradient m f x)^2 ∂m)+R f)
    (hsplit : ∀ f g : Lp ℝ 2 m,Sobolev m (f : X → ℝ) → Sobolev m (g : X → ℝ) →
      ∀ t : ℝ,R (f+t•g) ≤ 2*R f+2*t^2*R g)
    (hrelative : ∀ g : Lp ℝ 2 m,Sobolev m (g : X → ℝ) →
      2*R g ≤ ∫ x,cheegerHeat h (θ s) (u s) x*(weakGradient m g x)^2 ∂m)
    {A : ℝ} (hA : FormActionBound m (u s) v A) {ε : ℝ} (hε : 0 < ε)
    {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ} (hRf : R f ≤ E) :
    ∃ w : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z)) w s ∧
      HasDerivAt (fun z => ∫ x,regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m) e s ∧
      2*⟪w,f⟫_ℝ ≤ A/c+2*E-2*τ*e+
        ∫ x,(cheegerHeat h (θ s) (u s) x+ε)*(weakGradient m f x)^2 ∂m := by
  obtain ⟨L,hL,hD,hE⟩ := cheegerHeat_diagonal_entropy_hasDerivAt hfin h hθ hu hpos hε
  refine ⟨_,_,hD,hE,?_⟩
  have hPS (g : Lp ℝ 2 m) (hg : Sobolev m (g : X → ℝ)) :
      Sobolev m (cheegerHeat h (θ s) g) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h hpos.le g).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hg))
  have hP := hA.symmetric_contraction_error (cheegerHeat_symmetric h (θ s)) hPS hc hgrad
  have hPB := cheegerHeat_bounded h hpos.le hB (u s) hub
  have hPε : ∀ g : Lp ℝ 2 m,Sobolev m (g : X → ℝ) →
      2*⟪cheegerHeat h (θ s) v,g⟫_ℝ ≤ A/c+
        (∫ x,(cheegerHeat h (θ s) (u s) x+ε)*(weakGradient m g x)^2 ∂m)+R g := by
    intro g hg
    have H := integral_gradient_le_regularized (Lp.aestronglyMeasurable _) hPB hε.le hg
    linarith [hP g hg]
  have hLap := identified_isLaplacian_of_formGenerator hfin hID h _ _ hL
  let r := (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).toLp
    (fun x => regularizedLog ε (cheegerHeat h (θ s) (u s) x))
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae
    (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).coeFn_toLp).mpr
    (hLap.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
      (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  exact logarithmic_shift_split_absorb hfin hpar hLap
    (cheegerHeat_nonneg h hpos.le (u s) hun) hPB hε hPε τ hf hRf
    (hsplit f r hf hr τ)
    ((hrelative r hr).trans
      (integral_gradient_le_regularized (Lp.aestronglyMeasurable _) hPB hε.le hr))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_TestAction
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
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma hamiltonJacobi_slope_of_test_action
    {u W : ℝ → Lp ℝ 2 m} {s q A ε : ℝ} {v : Lp ℝ 2 m}
    (hu : HasDerivAt u v s) (hqs : 0 < q+s)
    (hS : Sobolev m (W s : X → ℝ))
    (hΓ : MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hun : ∀ z, s < z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ z, s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : 2*⟪v,W s⟫_ℝ ≤ A+∫ x,(u s x+ε)*(weakGradient m (W s) x)^2 ∂m) :
    ∀ r, (A+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r →
      ∀ᶠ z in 𝓝[>] s, slope (fun t => ⟪W t,u t⟫_ℝ) s z < r := by
  let Γ : Lp ℝ 2 m := hΓ.toLp (fun x => (weakGradient m (W s) x)^2)
  have hΓe : Γ =ᵐ[m] fun x => (weakGradient m (W s) x)^2 := hΓ.coeFn_toLp
  have hpair (z : ℝ) : ⟪Γ,u z⟫_ℝ = ∫ x, u z x*(weakGradient m (W s) x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΓe] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real]
  have hρΓ : Integrable (fun x => u s x*(weakGradient m (W s) x)^2) m :=
    (L2.integrable_inner (u s) Γ).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have hE : (∫ x, (u s x+ε)*(weakGradient m (W s) x)^2 ∂m) =
      ⟪Γ,u s⟫_ℝ+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hρΓ (hS.2.2.integrable_sq.const_mul ε),integral_const_mul,← hpair s]
  have hAa := hA
  rw [hE,real_inner_comm (W s) v] at hAa
  have hder : HasDerivAt (fun z => ⟪W s,u z⟫_ℝ) ⟪W s,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s (W s)).inner ℝ hu
  have hsl : Tendsto (slope (fun z => ⟪W s,u z⟫_ℝ) s) (𝓝[>] s) (𝓝 ⟪W s,v⟫_ℝ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] s) (𝓝 s) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun z => -(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      slope (fun z => ⟪W s,u z⟫_ℝ) s z) (𝓝[>] s)
      (𝓝 (-⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ)) := by
    have hdnom : Tendsto (fun z => 2*(q+z)) (𝓝[>] s) (𝓝 (2*(q+s))) :=
      (tendsto_const_nhds.add hid).const_mul 2
    have hpl : Tendsto (fun z => ⟪Γ,u z⟫_ℝ) (𝓝[>] s) (𝓝 ⟪Γ,u s⟫_ℝ) :=
      (continuousAt_const.inner hu.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have HH := (((tendsto_const_nhds (x := -(q+s))).div hdnom
      (by positivity : 2*(q+s) ≠ 0)).mul hpl).add hsl
    convert HH using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp [hqs.ne']
  intro r hr
  have hlt : -⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ < r := by linarith
  filter_upwards [hlim.eventually_lt_const hlt,self_mem_nhdsWithin] with z hz hzs
  change s < z at hzs
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field,slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hzs)).mpr
  have hiW : Integrable (fun x => (W z x-W s x)*u z x) m :=
    (L2.integrable_inner (u z) (W z)).sub (L2.integrable_inner (u z) (W s)) |>.congr (by
      filter_upwards [] with x
      simp only [RCLike.inner_apply,RCLike.conj_to_real,Pi.sub_apply]
      ring)
  have hiΓ : Integrable (fun x => (weakGradient m (W s) x)^2*u z x) m :=
    (L2.integrable_inner Γ (u z)).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have H := integral_mono_ae hiW (hiΓ.const_mul (-(z-s)*(q+s)/(2*(q+z)))) (by
    filter_upwards [hHJ z hzs,hun z hzs] with x hx hn
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx hn)
  have hI : (∫ x, (W z x-W s x)*u z x ∂m) = ⟪W z-W s,u z⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (W z) (W s)] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm,Pi.sub_apply]
  rw [hI,integral_const_mul] at H
  have hIΓ : (∫ x, (weakGradient m (W s) x)^2*u z x ∂m) = ⟪Γ,u z⟫_ℝ := by
    rw [hpair]; congr 1; funext x; ring
  rw [hIΓ,inner_sub_left] at H
  have he : (-(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      (⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ)/(z-s))*(z-s) =
      (-(z-s)*(q+s)/(2*(q+z)))*⟪Γ,u z⟫_ℝ+⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ := by
    field_simp [sub_ne_zero.mpr hzs.ne']; ring
  rw [he]
  linarith

lemma integrated_hamiltonJacobi_test_action
    {W u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {q τ ε D : ℝ}
    (hq : 0 < q) (hε : 0 ≤ ε)
    (hW : ContinuousOn W (Icc 0 1)) (hu : ContinuousOn u (Icc 0 1))
    (hE : ContinuousOn E (Icc 0 1)) (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hWS : ∀ s ∈ Ico (0:ℝ) 1, Sobolev m (W s : X → ℝ))
    (hΓ : ∀ s ∈ Ico (0:ℝ) 1, MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hD : ∀ s ∈ Ico (0:ℝ) 1, (∫ x, (weakGradient m (W s) x)^2 ∂m) ≤ D)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ s z, 0 ≤ s → s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      2*⟪v,W s⟫_ℝ ≤ a s-2*τ*e+∫ x,(u s x+ε)*(weakGradient m (W s) x)^2 ∂m) :
    ⟪W 1,u 1⟫_ℝ-⟪W 0,u 0⟫_ℝ+τ*(E 1-E 0) ≤ P 1-P 0+ε*D/2 := by
  choose v e hd he hA using hA
  let J := fun s => ⟪W s,u s⟫_ℝ
  let B := fun s => J 0+(P s-P 0)-τ*(E s-E 0)+ε*D/2*s
  let B' := fun s => if hs : s ∈ Ico (0:ℝ) 1 then a s/2-τ*(e s hs)+ε*D/2 else 0
  have hB : ContinuousOn B (Icc 0 1) := by
    exact (((continuousOn_const.add (hP.sub continuousOn_const)).sub
      ((hE.sub continuousOn_const).const_mul τ)).add (continuousOn_const.mul continuousOn_id))
  have hB' (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt B (B' s) (Ici s) s := by
    dsimp only [B']
    rw [dite_eq_left hs]
    convert! (((((hP' s hs).sub_const (P 0)).const_add (J 0)).sub
      (((he s hs).sub_const (E 0)).const_mul τ)).add
      ((hasDerivAt_id s).const_mul (ε*D/2))).hasDerivWithinAt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have H := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := J) (B := B) (B' := B') (hW.inner hu)
    (by dsimp [B]; simp) hB hB' (by
      intro s hs r hr
      change B' s < r at hr
      dsimp only [B'] at hr
      rw [dite_eq_left hs] at hr
      have hineq : (a s-2*τ*(e s hs)+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r := by
        have HH := mul_le_mul_of_nonneg_left (hD s hs) hε
        linarith
      exact (hamiltonJacobi_slope_of_test_action (hd s hs)
        (by linarith [hs.1]) (hWS s hs) (hΓ s hs)
        (fun z hz => hun z (by linarith [hs.1]))
        (fun z hz => hHJ s z hs.1 hz) (hA s hs) r hineq).frequently) ⟨zero_le_one,le_rfl⟩
  dsimp only [B,J] at H
  linarith

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PerturbedPlanDual
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

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma boundedHopfMap_lipschitz_uniform (f : X →ᵇ ℝ) {q t : ℝ}
    (hq : 0 < q) (ht : t ∈ Icc q (q+1)) :
    LipschitzWith ⟨hopfUniformLip f q,hopfUniformLip_nonneg f hq⟩ (boundedHopfMap f t : X → ℝ) := by
  have ht0 := hq.trans_le ht.1
  let D := Real.sqrt (4*(q+1)*‖f‖)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDs : D^2 = 4*(q+1)*‖f‖ := Real.sq_sqrt (by positivity)
  have H := hopfLax_lipschitz_radius f.continuous
    (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
    (by linarith [norm_nonneg f]) ht0 hD (by rw [hDs]; nlinarith [norm_nonneg f,ht.2])
  have hL : (⟨D/t+1/(2*t)+(‖f‖-(-‖f‖)),by simp only [sub_neg_eq_add]; positivity⟩ : ℝ≥0) ≤
      ⟨hopfUniformLip f q,hopfUniformLip_nonneg f hq⟩ := by
    change D/t+1/(2*t)+(‖f‖-(-‖f‖)) ≤ D/q+1/(2*q)+2*‖f‖
    have h1 := div_le_div_of_nonneg_left hD hq ht.1
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by positivity : 0 < 2*q) (by linarith [ht.1] : 2*q ≤ 2*t)
    linarith
  convert H.weaken hL using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact boundedHopfMap_apply_pos f ht0 x

omit [SigmaFinite m] in
lemma compact_dual_of_entropy_test_actions
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E : ℝ → ℝ → ℝ} {P a : ℝ → ℝ} {τ : ℝ}
    (hu : ContinuousOn u (Icc 0 1))
    (hE : ∀ ε, 0 < ε → ContinuousOn (E ε) (Icc 0 1))
    (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q)
    (hA : ∀ ε, 0 < ε → ∀ s ∈ Ico (0:ℝ) 1, ∀ w : Lp ℝ 2 m,
      Sobolev m (w : X → ℝ) →
      (∀ᵐ x ∂m,|weakGradient m w x| ≤ hopfUniformLip f q) →
      ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt (E ε) e s ∧
      2*⟪v,w⟫_ℝ ≤ a s-2*τ*e+∫ x,(u s x+ε)*(weakGradient m w x)^2 ∂m) :
    ∀ ε, 0 < ε →
      (∫ x, u 1 x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, u 0 x*boundedHopfMap f q x ∂m)+τ*(E ε 1-E ε 0) ≤ P 1-P 0+ε*compactHopfDualBound hfin o f hf hq/2 := by
  let data := compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)
  let W := data.choose
  obtain ⟨hWe,hWc,hWS,hΓ,hD,hHJ⟩ := data.choose_spec.choose_spec
  intro ε hε
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc 0 1) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_test_action (W := fun s => W (q+s)) hq hε.le
    (hWc.comp (by fun_prop) hmap) hu (hE ε hε) hP hP'
    (fun s hs => hWS _ (by linarith [hs.1]))
    (fun s hs => hΓ _ (by linarith [hs.1]))
    (fun s hs => hD _ (hmap ⟨hs.1,hs.2.le⟩)) hun
    (fun s z hs hsz => by
      have H := hHJ (q+s) (q+z) (by linarith) (by linarith)
      simpa only [add_sub_add_left_eq_sub] using H) (by
      intro s hs
      apply hA ε hε s hs _ (hWS _ (by linarith [hs.1]))
      filter_upwards [weakGradient_congr_ae (hWe (q+s) (by linarith [hs.1])),
        weakGradient_le_lipschitz hfin (boundedHopfMap_lipschitz_uniform f hq (hmap ⟨hs.1,hs.2.le⟩)),
        weakGradient_nonneg (m := m) (W (q+s))] with x he hb hn
      rw [abs_of_nonneg hn,he]; exact hb)
  have hpair (s : ℝ) (hs : 0 ≤ s) : ⟪W (q+s),u s⟫_ℝ =
      ∫ x, u s x*boundedHopfMap f (q+s) x ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWe (q+s) (by linarith)] with x hx
    simp only [W,hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair 1 zero_le_one,hpair 0 le_rfl] at H
  simpa only [add_zero,compactHopfDualBound,data] using H

lemma cheegerHeat_plan_entropy_dual_error_oai
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1)
    {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ))
    {b : ℝ → ℝ} (hbc : ContinuousOn b (Ici 0)) (hbp : ∀ t,0 ≤ t → 0 < b t)
    {R : ℝ → Lp ℝ 2 m → ℝ} {Eerror : ℝ}
    (hgrad : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
      b (backwardsHeatTime δ T s)*(∫ x,smoothDensity κ u s x*
        (weakGradient m (cheegerHeat h (backwardsHeatTime δ T s) v) x)^2 ∂m) ≤
        (∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)+R s v)
    (hsplit : ∀ s ∈ Ico (0:ℝ) 1, ∀ v w : Lp ℝ 2 m,Sobolev m (v : X → ℝ) → Sobolev m (w : X → ℝ) →
      ∀ t : ℝ,R s (v+t•w) ≤ 2*R s v+2*t^2*R s w)
    (hrelative : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      2*R s v ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)
    (herror : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      (∀ᵐ x ∂m,|weakGradient m v x| ≤ hopfUniformLip f q) → R s v ≤ Eerror) :
    ∀ ε, 0 < ε →
      (∫ x, cheegerHeat h δ (smoothDensity κ u 1) x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, cheegerHeat h (δ+T) (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) (smoothDensity κ u 0) x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ (smoothDensity κ u 1) x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, planKineticCost π/b (backwardsHeatTime δ T s)/2)+Eerror+
        ε*compactHopfDualBound hfin o f hf hq/2 := by
  let θ := backwardsHeatTime δ T
  let U := fun s => cheegerHeat h (θ s) (smoothDensity κ u s)
  let E := fun ε s => ∫ x, regularizedEntropy ε (U s x) ∂m
  let A := fun s => planKineticCost π/b (θ s)+2*Eerror
  let P := fun s => ∫ r in (0:ℝ)..s, A r/2
  have hθc : Continuous θ := by
    change Continuous (fun s => δ+T*max (1-s) 0); fun_prop
  have hbθ : Continuous (fun s => b (θ s)) := hbc.comp_continuous hθc (fun s => (backwardsHeatTime_pos hδ hT s).le)
  have hAcont : Continuous (fun s => A s/2) := by
    dsimp [A]
    exact ((continuous_const.div hbθ (fun s => (hbp _ (backwardsHeatTime_pos hδ hT s).le).ne')).add continuous_const).div_const 2
  have hPd (s : ℝ) : HasDerivAt P (A s/2) s :=
    intervalIntegral.integral_hasDerivAt_right (hAcont.intervalIntegrable 0 s)
      (hAcont.stronglyMeasurableAtFilter volume (𝓝 s)) hAcont.continuousAt
  have hUcont : Continuous U := by
    rw [continuous_iff_continuousAt]
    intro s
    exact cheegerHeat_tendsto_joint hfin h (backwardsHeatTime_pos hδ hT s)
      hθc.continuousAt ((smoothDensity_hasDerivAt hκ hc hu hnorm s).continuousAt)
  have hEc (ε : ℝ) (hε : 0 < ε) : Continuous (E ε) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (regularizedEntropy_hasFDeriv hε (U s)).continuousAt.comp hUcont.continuousAt
  have hprop := fun s => hπ.smoothDensity_properties hB hu hun hlaw hnorm
    hc.continuous (hc.continuous.integrable_of_hasCompactSupport hκ) hn hm s
  have hUn (s : ℝ) : ∀ᵐ x ∂m, 0 ≤ U s x :=
    cheegerHeat_nonneg h (backwardsHeatTime_pos hδ hT s).le _ (hprop s).1
  have hD := compact_dual_of_entropy_test_actions hfin o hUcont.continuousOn
    (fun ε hε => (hEc ε hε).continuousOn)
    (show ContinuousOn P (Icc 0 1) from (show Continuous P from
      continuous_iff_continuousAt.mpr fun s => (hPd s).continuousAt).continuousOn)
    (fun s _ => hPd s) (fun s _ => hUn s) f hf hq (τ := -T) (a := A) (E := E) (by
      intro ε hε s hs v hv hvb
      have HH := cheegerHeat_diagonal_entropy_test_error hfin hID hpar h
        (backwardsHeatTime_hasDerivAt δ T hs.2)
        (smoothDensity_hasDerivAt hκ hc hu hnorm s) (backwardsHeatTime_pos hδ hT s)
        B.coe_nonneg (hprop s).2.1 (hprop s).1 (hbp _ (backwardsHeatTime_pos hδ hT s).le)
        (hgrad s hs) (hsplit s hs) (hrelative s hs)
        (hπ.smoothDensity_action hfin hb hgeo hB hu hun hlaw hnorm hκ hc hn hm s) hε hv (herror s hs v hv hvb)
      exact HH)
  intro ε hε
  have H := hD ε hε
  have hθ0 : θ 0 = δ+T := by simp [θ,backwardsHeatTime]
  have hθ1 : θ 1 = δ := by simp [θ,backwardsHeatTime]
  have hInt : P 1 = (∫ r in (0:ℝ)..1,planKineticCost π/b (θ r)/2)+Eerror := by
    dsimp [P,A]
    simp_rw [add_div,show 2*Eerror/2 = Eerror by ring]
    have hkinc : Continuous (fun r => planKineticCost π/b (θ r)/2) :=
      (continuous_const.div hbθ (fun s => (hbp _ (backwardsHeatTime_pos hδ hT s).le).ne')).div_const 2
    rw [intervalIntegral.integral_add (hkinc.intervalIntegrable 0 1)
      (intervalIntegrable_const (c := Eerror)),intervalIntegral.integral_const]
    simp
  rw [hInt] at H
  dsimp only [U,E,P] at H
  rw [hθ0,hθ1,intervalIntegral.integral_same] at H
  linarith

end WeakHessian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error_oai.{u_1} := @OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error_oai.{u_1}
