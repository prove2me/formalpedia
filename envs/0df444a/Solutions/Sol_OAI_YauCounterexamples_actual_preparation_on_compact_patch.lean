-- Prove2me | solution 1 for OAI.YauCounterexamples.actual_preparation_on_compact_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:59:36.431442+00:00
-- url     : https://prove2.me/submissions/fa8bfcac-238f-4bcd-b348-77801f7c751f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.dualNorm
attribute [local instance] OAI.YauCounterexamples.dualSpace
omit [FiniteDimensional ℝ E] in

theorem quadraticPlaneStrict_eventually {H : CoordinateForm E} {a : E} (ha : a ≠ 0)
    (hs : quadraticPlaneStrict H a) : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), quadraticPlaneStrict p.1 p.2 := by
  obtain ⟨v,hv,hav,hpos⟩ := hs
  let w : CoordinateForm E × E → E := fun p => v - (inner ℝ p.2 v / ‖p.2‖ ^ 2) • p.2
  have han : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsnd : Continuous (fun p : CoordinateForm E × E => p.2) := continuous_snd
  have hw : ContinuousAt w (H,a) := by
    exact continuousAt_const.sub (((hsnd.inner continuous_const).continuousAt.div
      (hsnd.norm.pow 2).continuousAt han).smul hsnd.continuousAt)
  have hwa : w (H,a) = v := by simp [w,hav]
  let z : CoordinateForm E × E → E := fun p => ‖w p‖⁻¹ • w p
  have hz : ContinuousAt z (H,a) :=
    (hw.norm.inv₀ (by rw [hwa,hv]; norm_num)).smul hw
  have hza : z (H,a) = v := by simp [z,hwa,hv]
  have hp : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), 0 < p.1 (z p) (z p) := by
    have hc : ContinuousAt (fun p : CoordinateForm E × E => p.1 (z p) (z p)) (H,a) :=
      (continuousAt_fst.clm_apply hz).clm_apply hz
    apply hc.eventually (Ioi_mem_nhds ?_)
    simpa [hza] using hpos
  have hane : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), p.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually_ne ha
  have hwne : ∀ᶠ p : CoordinateForm E × E in 𝓝 (H,a), w p ≠ 0 :=
    hw.eventually_ne (by rw [hwa]; exact norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  filter_upwards [hp,hane,hwne] with p hp hpa hpw
  refine ⟨z p,?_,?_,hp⟩
  · simp [z,norm_smul,norm_ne_zero_iff.mpr hpw]
  · have hpn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hpa)
    have hwperp : inner ℝ p.2 (w p) = 0 := by
      simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
      ring
    simp [z,inner_smul_right,hwperp]

theorem isOpen_quadraticPlaneFull : IsOpen {p : CoordinateForm E × E | quadraticPlaneFull p.1 p.2} := by
  let S : Set E := sphere 0 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let B : Set ((CoordinateForm E × E) × S) := {p | inner ℝ p.1.2 (p.2 : E) = 0 ∧
    p.1.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : ((CoordinateForm E × E) × S) => p.1.1) := continuous_fst.fst
  have hv : Continuous (fun p : ((CoordinateForm E × E) × S) => (p.2 : E)) := continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.snd.inner (continuous_subtype_val.comp continuous_snd)) continuous_const
    · exact isClosed_le
        ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, B]
  constructor
  · intro hp
    rintro ⟨y,hy,hyp⟩
    subst p
    exact (not_le_of_gt (hp y.2 (by simpa only [S, mem_sphere_zero_iff_norm] using y.2.property) hy.1)) hy.2
  · intro hp v hv hav
    by_contra hh
    apply hp
    exact ⟨(p,⟨v,by simpa [S,mem_sphere_zero_iff_norm] using hv⟩),⟨hav,not_lt.mp hh⟩,rfl⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance genericHessMapNorm_r3b6970_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_r3b6970_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_r3b6970_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian


end

section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma second_directional_eq {f : E → V} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ f z w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply
    ((hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

lemma smooth_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (F ∘ y) z w) x v =
      fderiv ℝ (fderiv ℝ F) (y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      fderiv ℝ F (y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hdF := hF.differentiable (by simp)
  have hdy := hy.differentiable (by simp)
  have hdDF := (hF.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hdDy := (hy.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (F ∘ y) z w) =
      (fun z => fderiv ℝ F (y z) (fderiv ℝ y z w)) := by
    funext z
    rw [fderiv_comp z (hdF _) (hdy _),ContinuousLinearMap.comp_apply]
  rw [he]
  erw [fderiv_clm_apply ((hdDF _).comp x (hdy _))
    ((hdDy x).clm_apply (differentiableAt_const w))]
  erw [fderiv_fun_comp x (hdDF _) (hdy _)]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma smooth_product_second {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t*g t) z w) x v =
      f x * fderiv ℝ (fun z => fderiv ℝ g z w) x v +
      fderiv ℝ f x v * fderiv ℝ g x w +
      fderiv ℝ f x w * fderiv ℝ g x v +
      g x * fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t*g t) z w) =
      (fun z => f z * fderiv ℝ g z w + g z * fderiv ℝ f z w) := by
    funext z
    rw [fderiv_fun_mul (df z) (dg z)]
    simp
  rw [he]
  erw [fderiv_fun_add ((df x).mul ((dDg x).clm_apply (differentiableAt_const w)))
    ((dg x).mul ((dDf x).clm_apply (differentiableAt_const w))),
    fderiv_fun_mul (df x) ((dDg x).clm_apply (differentiableAt_const w)),
    fderiv_fun_mul (dg x) ((dDf x).clm_apply (differentiableAt_const w))]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

theorem corrugation_first {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v : E) :
    fderiv ℝ (fun z => ψ z+c*χ z*F (N • y z)) x v =
      fderiv ℝ ψ x v + c*fderiv ℝ χ x v*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v) := by
  have dhψ := hψ.differentiable (by simp) x
  have dhχ := hχ.differentiable (by simp) x
  have dhy := hy.differentiable (by simp) x
  have dhF := hF.differentiable (by simp) (N • y x)
  have dhny := dhy.const_smul N
  have dhcomp := dhF.comp x dhny
  erw [fderiv_fun_add dhψ ((dhχ.const_mul c).mul dhcomp),
    fderiv_fun_mul (dhχ.const_mul c) dhcomp,
    fderiv_const_mul dhχ c, fderiv_fun_comp x dhF dhny,
    fderiv_fun_const_smul dhy N]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_smul,smul_eq_mul,Function.comp_apply,Pi.smul_apply]
  ring


end

section
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma smooth_sum_second {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t+g t) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v +
      fderiv ℝ (fun z => fderiv ℝ g z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t+g t) z w) =
      (fun z => fderiv ℝ f z w + fderiv ℝ g z w) := by
    funext z; rw [fderiv_fun_add (df z) (dg z)]; rfl
  rw [he, fderiv_fun_add ((dDf x).clm_apply (differentiableAt_const w))
    ((dDg x).clm_apply (differentiableAt_const w))]
  rfl
lemma smooth_const_smul_second {f : E → V}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => c • f t) z w) x v =
      c • fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => c • f t) z w) =
      (fun z => c • fderiv ℝ f z w) := by
    funext z; rw [fderiv_fun_const_smul (df z) c]; rfl
  rw [he, fderiv_fun_const_smul ((dDf x).clm_apply (differentiableAt_const w)) c]
  rfl

lemma scaled_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v =
      N^2 * fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      N * fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hh := smooth_comp_second hF (hy.const_smul N) x v w
  change fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v = _ at hh
  rw [fderiv_fun_const_smul (hy.differentiable (by simp) x) N,
    smooth_const_smul_second hy N x v w] at hh
  simp only [_root_.smul_apply,map_smul,smul_eq_mul] at hh
  rw [hh]
  ring

theorem corrugation_second {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => ψ t+c*(χ t*F (N • y t))) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ ψ z w) x v +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*fderiv ℝ (fun z => fderiv ℝ χ z w) x v := by
  have hg : ContDiff ℝ ∞ (fun t => F (N • y t)) := hF.comp (hy.const_smul N)
  have hh := smooth_sum_second hψ ((hχ.mul hg).const_smul c) x v w
  simp only [smul_eq_mul] at hh
  rw [hh]
  have hc := smooth_const_smul_second (hχ.mul hg) c x v w
  simp only [smul_eq_mul] at hc
  rw [hc,smooth_product_second hχ hg x v w,scaled_comp_second hF hy N x v w]
  have hfirst (z : E) : fderiv ℝ (fun t => F (N • y t)) x z =
      N * fderiv ℝ F (N • y x) (fderiv ℝ y x z) := by
    erw [fderiv_fun_comp x (hF.differentiable (by simp) _) ((hy.differentiable (by simp) x).const_smul N),
      fderiv_fun_const_smul (hy.differentiable (by simp) x) N]
    simp
  rw [hfirst w,hfirst v]
  ring

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.prepDualNorm
attribute [local instance] OAI.YauCounterexamples.prepDualSpace
local instance prepFormNorm_r3b6970_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
attribute [local instance] OAI.YauCounterexamples.prepFormSpace
omit [FiniteDimensional ℝ E] in
lemma continuous_profileRankOne {X : Type*} [TopologicalSpace X]
    {l : X → E →L[ℝ] ℝ} (hl : Continuous l) : Continuous (fun x => profileRankOne (l x)) :=
  ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hl).clm_apply hl

omit [FiniteDimensional ℝ E] in
lemma continuous_metricProfileTraceForm_comp {X : Type*} [TopologicalSpace X]
    {B H : X → CoordinateForm E} {a : X → E}
    (hB : Continuous B) (hH : Continuous H) (ha : Continuous a) :
    Continuous (fun x => metricProfileTraceForm (B x) (H x) (a x)) := by
  unfold metricProfileTraceForm
  exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
    ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

lemma coordinateMetricGradient_ne_zero_dual (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) :
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 := by
  intro h
  have hd : fderiv ℝ u x = 0 := (InnerProductSpace.toDual ℝ E).symm.injective
    (by simpa only [map_zero] using h)
  apply ha
  simp only [coordinateMetricGradient,hd,map_zero]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PulledGradientNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinateCovariantSecond_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    coordinateCovariantSecond Γ f x v w =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v - fderiv ℝ f x (Γ x v w) := by
  rw [second_directional_eq hf]
  rfl

theorem corrugation_covariant_second
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    coordinateCovariantSecond Γ (fun z => ψ z+c*(χ z*F (N • y z))) x v w =
      coordinateCovariantSecond Γ ψ x v w +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  have hP : ContDiff ℝ ∞ (fun z => ψ z+c*(χ z*F (N • y z))) :=
    hψ.add (contDiff_const.mul (hχ.mul (hF.comp (hy.const_smul N))))
  have hfirst : fderiv ℝ (fun z => ψ z+c*(χ z*F (N • y z))) x (Γ x v w) =
      fderiv ℝ ψ x (Γ x v w) + c*fderiv ℝ χ x (Γ x v w)*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x (Γ x v w)) := by
    convert corrugation_first hψ hχ hF hy c N x (Γ x v w) using 1; congr 2
    funext z
    ring
  rw [coordinateCovariantSecond_apply Γ hP,
    corrugation_second hψ hχ hF hy,hfirst,
    coordinateCovariantSecond_apply Γ hψ,
    coordinateCovariantSecond_apply Γ hy,
    coordinateCovariantSecond_apply Γ hχ,map_sub]
  ring

lemma corrugationSecondRemainder_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x v w : E) :
    corrugationSecondRemainder Γ ψ χ F y d N x v w =
      d*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      d*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      d*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      (d/N)*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  change coordinateCovariantSecond Γ _ x v w - coordinateCovariantSecond Γ ψ x v w -
    (d*N*χ x)*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) = _
  rw [corrugation_covariant_second Γ hψ hχ hF hy]
  field_simp [hN]
  ring

theorem corrugationSecondRemainder_norm_bound
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x : E) :
    ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
      |d| * |χ x| * ‖fderiv ℝ F (N • y x)‖ * ‖coordinateCovariantSecond Γ y x‖ +
      2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖ * ‖fderiv ℝ y x‖ +
      |d / N| * |F (N • y x)| * ‖coordinateCovariantSecond Γ χ x‖ := by
  let DF := fderiv ℝ F (N • y x)
  let Dy := fderiv ℝ y x
  let Dχ := fderiv ℝ χ x
  let Hy := coordinateCovariantSecond Γ y x
  let Hχ := coordinateCovariantSecond Γ χ x
  apply (corrugationSecondRemainder Γ ψ χ F y d N x).opNorm_le_bound₂
    (by positivity)
  intro v w
  rw [corrugationSecondRemainder_apply Γ hψ hχ hF hy d N hN]
  have hyterm : ‖d * χ x * DF (Hy v w)‖ ≤
      |d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * |χ x| * (‖DF‖ * (‖Hy‖ * ‖v‖ * ‖w‖)) := by
        gcongr
        exact (DF.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (Hy.le_opNorm₂ v w) (norm_nonneg _))
      _ = _ := by ring
  have hcross (v w : E) : ‖d * Dχ v * DF (Dy w)‖ ≤
      |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * (‖Dχ‖ * ‖v‖) * (‖DF‖ * (‖Dy‖ * ‖w‖)) := by
        gcongr
        · exact Dχ.le_opNorm v
        · exact (DF.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (Dy.le_opNorm w) (norm_nonneg _))
      _ = _ := by ring
  have hχterm : ‖(d / N) * F (N • y x) * Hχ v w‖ ≤
      |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d / N| * |F (N • y x)| * (‖Hχ‖ * ‖v‖ * ‖w‖) := by
        gcongr
        exact Hχ.le_opNorm₂ v w
      _ = _ := by ring
  calc
    _ ≤ (‖d * χ x * DF (Hy v w)‖ + ‖d * Dχ v * DF (Dy w)‖ +
        ‖d * Dχ w * DF (Dy v)‖) + ‖(d / N) * F (N • y x) * Hχ v w‖ :=
      (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (|d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖w‖ * ‖v‖) +
        |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ :=
      add_le_add (add_le_add (add_le_add hyterm (hcross v w)) (hcross w v)) hχterm
    _ = _ := by dsimp [DF, Dy, Dχ, Hy, Hχ]; ring


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Function
open scoped Topology ContDiff
variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_translate {f : V → F} (hf : ContDiff ℝ ∞ f) (τ : V) :
    ContDiff ℝ ∞ (fun v => f (v+τ)) := hf.comp (contDiff_id.add contDiff_const)

lemma fderiv_translate {f : V → F} (hf : ContDiff ℝ ∞ f) (τ z : V) :
    fderiv ℝ (fun v => f (v+τ)) z = fderiv ℝ f (z+τ) := by
  have hh : HasFDerivAt (fun v : V => v+τ) (ContinuousLinearMap.id ℝ V) z := by
    simpa using (hasFDerivAt_id z).add_const τ
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using ((hf.differentiable (by simp) (z+τ)).hasFDerivAt.comp z hh).fderiv

theorem preparation_remainder_uniform_phase
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B₀ B₁ : ℝ)
    (hB₀ : ∀ z, |F₀ z| ≤ B₀) (hB₁ : ∀ z, ‖fderiv ℝ F₀ z‖ ≤ B₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ), 1 ≤ N → ∀ τ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ (fun z => F₀ (z+τ)) y (d/N) N x‖ ≤ C/N := by
  obtain ⟨Y₂,hY₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ y)
    (continuous_coordinateCovariantSecond Γ hΓ hy).continuousOn
  obtain ⟨Y₁,hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y) (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₂,hD₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ χ)
    (continuous_coordinateCovariantSecond Γ hΓ hχ).continuousOn
  obtain ⟨D₁,hD₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ χ) (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₀,hD₀⟩ := hK.exists_bound_of_continuousOn (f := χ) hχ.continuous.continuousOn
  let A := |d| *|D₀| *|B₁| *|Y₂| +2*|d| *|D₁| *|B₁| *|Y₁| +|d| *|B₀| *|D₂|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,?_⟩
  intro N hN τ x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY₂x := (hY₂ x hx).trans (le_abs_self Y₂)
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hD₂x := (hD₂ x hx).trans (le_abs_self D₂)
  have hD₁x := (hD₁ x hx).trans (le_abs_self D₁)
  have hD₀x : |χ x| ≤ |D₀| := (hD₀ x hx).trans (le_abs_self D₀)
  have hF₀x := (hB₀ (N • y x+τ)).trans (le_abs_self B₀)
  have hF₁x : ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖ ≤ |B₁| := by
    rw [fderiv_translate hF]
    exact (hB₁ _).trans (le_abs_self B₁)
  have he : |d/N/N| ≤ |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    exact div_le_self (div_nonneg (abs_nonneg _) hNp.le) hN
  calc
    _ ≤ |d/N| *|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖coordinateCovariantSecond Γ y x‖ +
        2*|d/N| *‖fderiv ℝ χ x‖*‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖ +
        |d/N/N| *|F₀ (N • y x+τ)| *‖coordinateCovariantSecond Γ χ x‖ :=
      corrugationSecondRemainder_norm_bound Γ hψ hχ (smooth_translate hF τ) hy (d/N) N hNp.ne' x
    _ ≤ (|d|/N)*|D₀| *|B₁| *|Y₂| +2*(|d|/N)*|D₁| *|B₁| *|Y₁| +(|d|/N)*|B₀| *|D₂| := by
      rw [abs_div,abs_of_pos hNp]
      gcongr
    _ = A/N := by dsimp [A]; ring
    _ ≤ (A+1)/N := div_le_div_of_nonneg_right (by linarith) hNp.le

theorem preparation_C1_uniform_phase
    {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B₀ B₁ : ℝ)
    (hB₀ : ∀ z, |F₀ z| ≤ B₀) (hB₁ : ∀ z, ‖fderiv ℝ F₀ z‖ ≤ B₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ), 1 ≤ N → ∀ τ : V, ∀ x ∈ K,
      |preparationCorrugation ψ χ F₀ y d N τ x-ψ x| ≤ C/N ∧
      ‖fderiv ℝ (preparationCorrugation ψ χ F₀ y d N τ) x-fderiv ℝ ψ x‖ ≤ C/N := by
  obtain ⟨Y₁,hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y)
    (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₁,hD₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ χ)
    (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₀,hD₀⟩ := hK.exists_bound_of_continuousOn (f := χ) hχ.continuous.continuousOn
  let A := |d| * |D₀| * |B₀| + |d| * |D₁| * |B₀| + |d| * |D₀| * |B₁| * |Y₁|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,?_⟩
  intro N hN τ x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hD₁x := (hD₁ x hx).trans (le_abs_self D₁)
  have hD₀x : |χ x| ≤ |D₀| := (hD₀ x hx).trans (le_abs_self D₀)
  have hF₀x := (hB₀ (N • y x+τ)).trans (le_abs_self B₀)
  have hF₁x : ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖ ≤ |B₁| := by
    rw [fderiv_translate hF]
    exact (hB₁ _).trans (le_abs_self B₁)
  have he : |d/N/N| ≤ |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    exact div_le_self (div_nonneg (abs_nonneg _) hNp.le) hN
  have heN : |d/N/N| *N = |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    field_simp
  have hC : (|d| *|D₀| *|B₀|)/N ≤ (A+1)/N := by
    apply div_le_div_of_nonneg_right _ hNp.le
    dsimp [A]
    nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₁)) (abs_nonneg B₀),
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₀)) (abs_nonneg B₁)) (abs_nonneg Y₁)]
  constructor
  · calc
      _ = |d/N/N| * |χ x| * |F₀ (N • y x+τ)| := by
        simp only [preparationCorrugation,add_sub_cancel_left,abs_mul]; ring
      _ ≤ (|d|/N)*|D₀| *|B₀| := by gcongr
      _ = (|d| *|D₀| *|B₀|)/N := by ring
      _ ≤ (A+1)/N := hC
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hdv : (fderiv ℝ (preparationCorrugation ψ χ F₀ y d N τ) x-fderiv ℝ ψ x) v =
        (d/N/N)*fderiv ℝ χ x v*F₀ (N • y x+τ)+
        (d/N/N)*χ x*N*fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v) := by
      have hh := corrugation_first hψ hχ (smooth_translate hF τ) hy (d/N/N) N x v
      have heq : preparationCorrugation ψ χ F₀ y d N τ =
          fun z => ψ z+(d/N/N)*χ z*F₀ (N • y z+τ) := by
        funext z; dsimp [preparationCorrugation]; ring
      rw [heq,sub_apply,hh]
      ring
    rw [hdv]
    calc
      _ ≤ |d/N/N| *‖fderiv ℝ χ x‖*‖v‖*|F₀ (N • y x+τ)|+
          |d/N/N| *|χ x| *N*‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖ := by
        have hbχ : |fderiv ℝ χ x v| ≤ ‖fderiv ℝ χ x‖*‖v‖ := (fderiv ℝ χ x).le_opNorm v
        have hbF : |fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v)| ≤
            ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*(‖fderiv ℝ y x‖*‖v‖) :=
          ((fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((fderiv ℝ y x).le_opNorm v) (norm_nonneg _))
        calc
          _ ≤ |d/N/N| * |fderiv ℝ χ x v| * |F₀ (N • y x+τ)|+
              |d/N/N| * |χ x| * N * |fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v)| := by
            simpa only [norm_mul,Real.norm_eq_abs,abs_of_pos hNp] using norm_add_le
              ((d/N/N)*fderiv ℝ χ x v*F₀ (N • y x+τ))
              ((d/N/N)*χ x*N*fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v))
          _ ≤ |d/N/N| * (‖fderiv ℝ χ x‖*‖v‖) * |F₀ (N • y x+τ)|+
              |d/N/N| * |χ x| * N * (‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*(‖fderiv ℝ y x‖*‖v‖)) := by gcongr
          _ = _ := by ring
      _ = |d/N/N| *‖fderiv ℝ χ x‖*‖v‖*|F₀ (N • y x+τ)|+
          (|d|/N)*|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖ := by
        have hh := congrArg (fun t => t*|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖) heN
        nlinarith only [hh]
      _ ≤ (|d|/N)*|D₁| *‖v‖*|B₀|+(|d|/N)*|D₀| *|B₁| *|Y₁| *‖v‖ := by gcongr
      _ = ((|d| *|D₁| *|B₀|+|d| *|D₀| *|B₁| *|Y₁|)/N)*‖v‖ := by ring
      _ ≤ ((A+1)/N)*‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        apply div_le_div_of_nonneg_right _ hNp.le
        dsimp [A]
        nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₀)) (abs_nonneg B₀)]

end YauCounterexamples

end

open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma preparationWave_smooth : ContDiff ℝ ∞ preparationWave :=
  ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).neg).div_const _

lemma preparationWave_hasDeriv (t : ℝ) : HasDerivAt preparationWave (preparationWaveFirst t) t := by
  have hb : HasDerivAt (fun z : ℝ => 2*Real.pi*z) (2*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2*Real.pi)
  have hh := hb.cos.neg.div_const (2*Real.pi^2)
  have he : -(-Real.sin (2*Real.pi*t)*(2*Real.pi))/(2*Real.pi^2) = preparationWaveFirst t := by
    dsimp [preparationWaveFirst]
    field_simp [Real.pi_ne_zero]
  rw [he] at hh
  exact hh

lemma preparationWaveFirst_hasDeriv (t : ℝ) :
    HasDerivAt preparationWaveFirst (preparationWaveSecond t) t := by
  have hb : HasDerivAt (fun z : ℝ => 2*Real.pi*z) (2*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2*Real.pi)
  have hh := hb.sin.div_const Real.pi
  have he : Real.cos (2*Real.pi*t)*(2*Real.pi)/Real.pi = preparationWaveSecond t := by
    dsimp [preparationWaveSecond]
    field_simp [Real.pi_ne_zero]
  rw [he] at hh
  exact hh

lemma preparationWave_deriv : deriv preparationWave = preparationWaveFirst := by
  funext t
  exact (preparationWave_hasDeriv t).deriv

lemma preparationWave_second : deriv (deriv preparationWave) = preparationWaveSecond := by
  rw [preparationWave_deriv]
  funext t
  exact (preparationWaveFirst_hasDeriv t).deriv

lemma preparationWave_abs_bound (t : ℝ) : |preparationWave t| ≤ 1/(2*Real.pi^2) := by
  dsimp [preparationWave]
  rw [abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi^2)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

lemma preparationWave_deriv_bound (t : ℝ) : ‖fderiv ℝ preparationWave t‖ ≤ 1/Real.pi := by
  rw [←norm_deriv_eq_norm_fderiv,preparationWave_deriv]
  dsimp [preparationWaveFirst]
  rw [abs_div,abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) Real.pi_pos.le

lemma preparationWave_second_bound (t : ℝ) : |preparationWaveSecond t| ≤ 2 := by
  dsimp [preparationWaveSecond]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [Real.abs_cos_le_one (2*Real.pi*t)]

lemma scalar_second_fderiv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t v w : ℝ) :
    fderiv ℝ (fderiv ℝ f) t v w = deriv (deriv f) t * v * w := by
  have hh : (fun z => fderiv ℝ f z w) = fun z => deriv f z*w := by
    funext z
    exact fderiv_eq_deriv_mul
  have he : fderiv ℝ (fun z => fderiv ℝ f z w) t =
      (fderiv ℝ (fderiv ℝ f) t).flip w := by
    rw [fderiv_clm_apply
      ((hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp) t)
      (differentiableAt_const w)]
    simp
  rw [←ContinuousLinearMap.flip_apply,←he,hh]
  have hd : ContDiff ℝ ∞ (deriv f) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_mul_const (hd.differentiable (by simp) t)]
  simp only [smul_apply,smul_eq_mul,fderiv_eq_deriv_mul]
  ring

end YauCounterexamples

end


end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.jetDualNorm
attribute [local instance] OAI.YauCounterexamples.jetDualSpace
lemma contDiff_selfMetricFlat_inverse (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
    (contDiff_selfMetricFlat g).contDiffAt

lemma continuous_metricJetMap (g : SmoothMetric E E) : Continuous (metricJetMap g) := by
  have hB : Continuous (fun z : MetricJet E => selfMetricFlat g z.1) :=
    (contDiff_selfMetricFlat g).continuous.comp continuous_fst
  have ha : Continuous (fun z : MetricJet E => (selfMetricFlat g z.1).inverse z.2.2) :=
    ((contDiff_selfMetricFlat_inverse g).continuous.comp continuous_fst).clm_apply continuous_snd.snd
  exact (continuous_metricProfileTraceForm_comp hB continuous_snd.fst ha).prodMk
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp continuous_snd.snd)

lemma isOpen_metricJetStrict (g : SmoothMetric E E) : IsOpen {z | metricJetStrict g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneStrict p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (continuous_snd.continuousAt.eventually_ne hp.1).and
      (quadraticPlaneStrict_eventually hp.1 hp.2)
  exact h.preimage (continuous_metricJetMap g)

lemma isOpen_metricJetFull (g : SmoothMetric E E) : IsOpen {z | metricJetFull g z} := by
  have h : IsOpen {p : CoordinateForm E × E | p.2 ≠ 0 ∧ quadraticPlaneFull p.1 p.2} :=
    (isOpen_ne_fun continuous_snd continuous_const).inter isOpen_quadraticPlaneFull
  exact h.preimage (continuous_metricJetMap g)

omit [FiniteDimensional ℝ E] in
theorem compact_metricJet_stability (_g : SmoothMetric E E) (P : MetricJet E → Prop)
    (hP : IsOpen {z | P z}) {K : Set E} (hK : IsCompact K) {J : Set ℝ} (hJ : IsCompact J)
    {H : E × ℝ → CoordinateForm E} (hH : Continuous H)
    {l : E → E →L[ℝ] ℝ} (hl : Continuous l)
    (hgood : ∀ x ∈ K, ∀ c ∈ J, P (x,H (x,c),l x)) :
    ∃ ε > 0, ∀ x ∈ K, ∀ c ∈ J, ∀ H' : CoordinateForm E, ∀ l' : E →L[ℝ] ℝ,
      ‖H'-H (x,c)‖ < ε → ‖l'-l x‖ < ε → P (x,H',l') := by
  let : PseudoEMetricSpace (MetricJet E) :=
    (inferInstance : PseudoMetricSpace (MetricJet E)).toPseudoEMetricSpace
  let f : E × ℝ → MetricJet E := fun z => (z.1,H z,l z.1)
  have hf : Continuous f := continuous_fst.prodMk (hH.prodMk (hl.comp continuous_fst))
  have hc := (hK.prod hJ).image hf
  have hsub : f '' (K ×ˢ J) ⊆ {z | P z} := by
    rintro z ⟨⟨x,c⟩,hx,rfl⟩
    exact hgood x hx.1 c hx.2
  obtain ⟨ε,hε,he⟩ := hc.exists_thickening_subset_open hP hsub
  refine ⟨ε,hε,?_⟩
  intro x hx c hc H' l' hH' hl'
  apply he
  apply mem_thickening_iff.mpr
  refine ⟨f (x,c),mem_image_of_mem f ⟨hx,hc⟩,?_⟩
  change dist (x,H',l') (x,H (x,c),l x) < ε
  rw [Prod.dist_eq,Prod.dist_eq,dist_self]
  exact max_lt hε (max_lt (by simpa only [dist_eq_norm] using hH')
    (by simpa only [dist_eq_norm] using hl'))

lemma metricJetStrict_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetStrict g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileStrict g u x := by
  have hn : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 ↔
      coordinateMetricGradient g u x ≠ 0 := by
    constructor
    · intro hh h0
      have hd : fderiv ℝ u x = 0 := by
        simpa only [map_zero] using (selfMetricFlat_invertible g x).inverse_apply_eq.mp h0
      exact hh (by simp only [hd,map_zero])
    · exact coordinateMetricGradient_ne_zero_dual g u x
  exact and_congr_left (fun _ => hn)

lemma metricJetFull_actual (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    metricJetFull g (x,actualCoordinateHessian g u x,fderiv ℝ u x) ↔
      coordinateMetricGradient g u x ≠ 0 ∧ actualProfileFull g u x := by
  have hn : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 ↔
      coordinateMetricGradient g u x ≠ 0 := by
    constructor
    · intro hh h0
      have hd : fderiv ℝ u x = 0 := by
        simpa only [map_zero] using (selfMetricFlat_invertible g x).inverse_apply_eq.mp h0
      exact hh (by simp only [hd,map_zero])
    · exact coordinateMetricGradient_ne_zero_dual g u x
  exact and_congr_left (fun _ => hn)


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_OscDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma preparationWave_second_translate (τ t v w : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => preparationWave (z+τ))) t v w =
      preparationWaveSecond (t+τ)*v*w := by
  rw [scalar_second_fderiv (smooth_translate preparationWave_smooth τ)]
  have he : deriv (fun z => preparationWave (z+τ)) = fun z => deriv preparationWave (z+τ) := by
    funext z
    exact deriv_comp_add_const (f:=preparationWave) (a:=τ) (x:=z)
  rw [he,deriv_comp_add_const,preparationWave_second]

lemma preparation_hessian_remainder_eq (g : SmoothMetric E E) (u χ s : E → ℝ)
    (C N τ : ℝ) (hN : N ≠ 0) (x : E) :
    actualCoordinateHessian g (preparationCorrugation u χ preparationWave s C N τ) x-
      (actualCoordinateHessian g u x+
        (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x)) =
      corrugationSecondRemainder (metricChristoffel g) u χ (fun z => preparationWave (z+τ)) s
        (C/N) N x := by
  have he : ((C/N)*N*χ x) •
        (fderiv ℝ (fderiv ℝ (fun z => preparationWave (z+τ))) (N • s x)).bilinearComp
          (fderiv ℝ s x) (fderiv ℝ s x) =
      (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x) := by
    ext v w
    simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
      preparationWave_second_translate,profileRankOne_apply]
    field_simp
  rw [corrugationSecondRemainder,he]
  change coordinateCovariantSecond (metricChristoffel g)
    (fun z => u z+(C/N/N)*(χ z*preparationWave (N • s z+τ))) x-
    (coordinateCovariantSecond (metricChristoffel g) u x+_) = _
  abel

local instance oscDualNorm_r3b6970_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.oscDualSpace
theorem preparation_hessian_uniform (g : SmoothMetric E E)
    {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
    (K : Set E) (hK : IsCompact K) (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℝ, 1 ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
      ‖actualCoordinateHessian g (preparationCorrugation u χ preparationWave s C N τ) x-
        (actualCoordinateHessian g u x+
          (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x))‖ ≤ A/N := by
  obtain ⟨A,hA,hbound⟩ := preparation_remainder_uniform_phase
    (metricChristoffel g) (contDiff_metricChristoffel g).continuous hu hχ preparationWave_smooth hs
    K hK C (1/(2*Real.pi^2)) (1/Real.pi) preparationWave_abs_bound preparationWave_deriv_bound
  refine ⟨A,hA,?_⟩
  intro N hN τ x hx
  rw [preparation_hessian_remainder_eq g u χ s C N τ (ne_of_gt (lt_of_lt_of_le zero_lt_one hN)) x]
  exact hbound N hN τ x hx

theorem actual_preparation_on_compact_patch_oai (g : SmoothMetric E E)
    {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
    {K : Set E} (hK : IsCompact K) (C : ℝ) (hC : 0 < C)
    (hcut : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
    (hq : ∀ x ∈ K, (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0)
    (hstrict : ∀ x ∈ K, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (hfull : ∀ x ∈ K, ∀ c ∈ Icc C (2*C), quadraticPlaneFull
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
      let u' := preparationCorrugation u χ preparationWave s C N τ
      coordinateMetricGradient g u' x ≠ 0 ∧ actualProfileStrict g u' x ∧
      (χ x = 1 → 1 < preparationWaveSecond (N*s x+τ) → actualProfileFull g u' x) ∧
      |u' x-u x| < ε ∧ ‖fderiv ℝ u' x-fderiv ℝ u x‖ < ε := by
  let H : E × ℝ → CoordinateForm E := fun z => actualCoordinateHessian g u z.1+
    z.2 • profileRankOne (fderiv ℝ s z.1)
  have hH : Continuous H :=
    ((continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu).comp
      continuous_fst).add (continuous_snd.smul
        (continuous_profileRankOne ((hs.continuous_fderiv (by simp)).comp continuous_fst)))
  have hl : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  obtain ⟨δS,hδS,hS⟩ := compact_metricJet_stability g (metricJetStrict g)
    (isOpen_metricJetStrict g) hK (isCompact_Icc (a:=(-2*C)) (b:=2*C)) hH hl
    (fun x hx c hc => ⟨hq x hx,hstrict x hx c hc⟩)
  obtain ⟨δF,hδF,hF⟩ := compact_metricJet_stability g (metricJetFull g)
    (isOpen_metricJetFull g) hK (isCompact_Icc (a:=C) (b:=2*C)) hH hl
    (fun x hx c hc => ⟨hq x hx,hfull x hx c hc⟩)
  let δ := min ε (min δS δF)
  have hδ : 0 < δ := lt_min hε (lt_min hδS hδF)
  obtain ⟨A₁,hA₁,h₁⟩ := preparation_C1_uniform_phase hu hχ preparationWave_smooth hs
    K hK C (1/(2*Real.pi^2)) (1/Real.pi) preparationWave_abs_bound preparationWave_deriv_bound
  obtain ⟨A₂,hA₂,h₂⟩ := preparation_hessian_uniform g hu hχ hs K hK C
  let N₀ := max 1 ((A₁+A₂)/δ+1)
  refine ⟨N₀,le_max_left _ _,?_⟩
  intro N hN τ x hx
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hlarge : (A₁+A₂)/δ < N := by
    have hh := (le_max_right 1 ((A₁+A₂)/δ+1)).trans hN
    linarith
  have hsmall : (A₁+A₂)/N < δ := by
    rw [div_lt_iff₀ hNp]
    have hh := (div_lt_iff₀ hδ).mp hlarge
    linarith
  have hsmall₁ : A₁/N < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hNp.le) hsmall
  have hsmall₂ : A₂/N < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hNp.le) hsmall
  obtain ⟨hC0,hC1⟩ := h₁ N hN1 τ x hx
  have hHs := h₂ N hN1 τ x hx
  let c := C*χ x*preparationWaveSecond (N*s x+τ)
  have hcb : |c| ≤ 2*C := by
    dsimp [c]
    rw [abs_mul,abs_mul,abs_of_pos hC,abs_of_nonneg (hcut x hx).1]
    calc
      _ ≤ C*1*2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hcut x hx).2 hC.le
        · exact preparationWave_second_bound _
        · exact abs_nonneg _
        · positivity
      _ = _ := by ring
  have hc : c ∈ Icc (-2*C) (2*C) := by
    constructor <;> linarith [(abs_le.mp hcb).1,(abs_le.mp hcb).2]
  have hs' := hS x hx c hc _ _
    ((hHs.trans_lt hsmall₂).trans_le (min_le_right _ _ |>.trans (min_le_left _ _)))
    ((hC1.trans_lt hsmall₁).trans_le (min_le_right _ _ |>.trans (min_le_left _ _)))
  have hgood := (metricJetStrict_actual g _ x).mp hs'
  refine ⟨hgood.1,hgood.2,?_,(hC0.trans_lt hsmall₁).trans_le (min_le_left _ _),
    (hC1.trans_lt hsmall₁).trans_le (min_le_left _ _)⟩
  intro hx1 hw
  have hcf : c ∈ Icc C (2*C) := by
    refine ⟨?_,hc.2⟩
    dsimp [c]
    rw [hx1,mul_one]
    nlinarith
  have hf' := hF x hx c hcf _ _
    ((hHs.trans_lt hsmall₂).trans_le (min_le_right _ _ |>.trans (min_le_right _ _)))
    ((hC1.trans_lt hsmall₁).trans_le (min_le_right _ _ |>.trans (min_le_right _ _)))
  exact ((metricJetFull_actual g _ x).mp hf').2

end
end YauCounterexamples

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.actual_preparation_on_compact_patch_oai.{u_1} := @OAI.YauCounterexamples.actual_preparation_on_compact_patch_oai.{u_1}
