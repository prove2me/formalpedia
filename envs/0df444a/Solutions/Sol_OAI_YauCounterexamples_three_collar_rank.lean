-- Prove2me | solution 1 for OAI.YauCounterexamples.three_collar_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:35:45.889264+00:00
-- url     : https://prove2.me/submissions/10bc7dfe-830d-4120-8a02-2a6b5295e94f

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_gradient_value
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_profile_rank_somewhere

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LinearProdSurjectiveMinor
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
lemma linear_prod_surjective_of_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L R : E →L[ℝ] ℝ) (v w : E) (h : L v*R w-L w*R v ≠ 0) :
    Function.Surjective (L.prod R) := by
  rintro ⟨a,b⟩
  let D := L v*R w-L w*R v
  refine ⟨((a*R w-b*L w)/D) • v+((b*L v-a*R v)/D) • w, ?_⟩
  apply Prod.ext
  · change L (_ • v+_ • w)=a
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      _ = a*D/D := by dsimp only [D]; ring
      _ = a := mul_div_cancel_right₀ a h
  · change R (_ • v+_ • w)=b
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      _ = b*D/D := by dsimp only [D]; ring
      _ = b := mul_div_cancel_right₀ b h
lemma analytic_rank_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g)
    {x₀ : E} (hr : Function.Surjective (fderiv ℝ (fun x => (f x,g x)) x₀))
    {O : Set E} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y ∈ O, Function.Surjective (fderiv ℝ (fun x => (f x,g x)) y) := by
  have hd (x : E) : fderiv ℝ (fun x => (f x,g x)) x = (fderiv ℝ f x).prod (fderiv ℝ g x) :=
    (hf.differentiable (by simp) x).fderiv_prodMk (hg.differentiable (by simp) x)
  obtain ⟨v,hv⟩ := hr (1,0)
  obtain ⟨w,hw⟩ := hr (0,1)
  rw [hd] at hv hw
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  have hw1 := congrArg Prod.fst hw
  have hw2 := congrArg Prod.snd hw
  simp only [ContinuousLinearMap.prod_apply] at hv1 hv2 hw1 hw2
  let D : E → ℝ := fun x => fderiv ℝ f x v*fderiv ℝ g x w-fderiv ℝ f x w*fderiv ℝ g x v
  have hD : ContDiff ℝ ω D := by
    have H (q : E → ℝ) (hq : ContDiff ℝ ω q) (z : E) :
        ContDiff ℝ ω (fun x => fderiv ℝ q x z) :=
      (hq.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
    exact ((H f hf v).mul (H g hg w)).sub ((H f hf w).mul (H g hg v))
  by_contra! hn
  obtain ⟨z,hz⟩ := hne
  have he : D =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [hO.mem_nhds hz] with x hx
    by_contra hh
    apply hn x hx
    rw [hd]
    exact linear_prod_surjective_of_minor _ _ v w hh
  have hglo := hD.analyticOnNhd.eq_of_eventuallyEq contDiff_const.analyticOnNhd he
  have := congrFun hglo x₀
  simp only [D,hv1,hv2,hw1,hw2] at this
  norm_num at this
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl


end

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
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairCongrNhds
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
section LocalPair
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (he : u =ᶠ[𝓝 x] v) : coordinateGradientPair g u u x = coordinateGradientPair g v v x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source _ _)] using (c.continuousAt_symm hx).tendsto
  have hd : fderiv ℝ (u ∘ c.symm) (c x) = fderiv ℝ (v ∘ c.symm) (c x) :=
    (he.comp_tendsto ht).fderiv_eq
  dsimp only [c] at hd
  simp only [coordinateGradientPair,hd]
end LocalPair



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ThreeProjectionNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
lemma coordinateGradientPair_metric_point_eq {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g h : SmoothMetric E M) (p : M)
    (he : ∀ v w : TangentSpace 𝓘(ℝ,E) p, g.inner p v w=h.inner p v w)
    (u v : M → ℝ) : coordinateGradientPair g u v p=coordinateGradientPair h u v p := by
  have hp := (chartAt E p).left_inv (mem_chart_source E p)
  have hm : metricCoefficients g p ((chartAt E p) p)=metricCoefficients h p ((chartAt E p) p) := by
    unfold metricCoefficients
    have hh : ∀ q, q=p → ∀ a b : TangentSpace 𝓘(ℝ,E) q, g.inner q a b=h.inner q a b := by
      intro q hq; subst q; exact he
    funext i j
    exact hh _ hp _ _
  simp only [coordinateGradientPair,hm]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeAnalyticNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeAnalyticNormedSpace
local instance threeAnalyticContinuousSMul_r4c9782_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma three_chart_sphere_analytic (p : ThreeManifold) :
    ContDiff ℝ ω (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).1:Euclidean 3)) := by
  have he : (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).1:Euclidean 3))=
      fun y => roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst := by
    funext y
    exact congrArg (fun q : ThreeAmbient => q.fst) (congrFun (three_chart_symm p) y)
  rw [he]
  exact (contDiff_stereoInvFunAux.comp (sphereFrame p.1).toContinuousLinearMap.contDiff).comp
    (WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
local instance threeAnalytic_dimension_fact_r4c9782_1 (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma three_chart_circle_analytic (p : ThreeManifold) :
    ContDiff ℝ ω (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).2:ℂ)) := by
  have he : (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).2:ℂ))=
      fun y => roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd := by
    funext y
    exact congrArg (fun q : ThreeAmbient => q.snd) (congrFun (three_chart_symm p) y)
  rw [he]
  exact (contDiff_stereoInvFunAux.comp (unitSphereFrame (n:=1) p.2).toContinuousLinearMap.contDiff).comp
    (WithLp.sndL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma threeCoupled_chart_analytic (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ω (threeCoupled r k ∘ (chartAt ThreeModel p).symm) := by
  have hA := (planarLinear (productAxis 0) (productAxis 1)).contDiff.comp (three_chart_sphere_analytic p)
  have hB := (planarLinear (productAxis 0) (productAxis 2)).contDiff.comp (three_chart_sphere_analytic p)
  have hz := three_chart_circle_analytic p
  exact Complex.reCLM.contDiff.comp (((hA.pow k).add (contDiff_const.mul (hB.pow k))).mul (hz.pow k))
lemma threeCoupled_gradient_chart_analytic (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
    ContDiff ℝ ω (coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) ∘
      (chartAt ThreeModel p).symm) := by
  have hA := (planarLinear (productAxis 0) (productAxis 1)).contDiff.comp (three_chart_sphere_analytic p)
  have hB := (planarLinear (productAxis 0) (productAxis 2)).contDiff.comp (three_chart_sphere_analytic p)
  have hz := three_chart_circle_analytic p
  have hα := (hz.pow k).mul (hA.pow (k-1))
  have hβ := ((hz.pow k).mul (contDiff_const (c:=(r:ℂ)^k))).mul (hB.pow (k-1))
  have hC := ((hA.pow k).add ((contDiff_const (c:=(r:ℂ)^k)).mul (hB.pow k))).mul (hz.pow k)
  have hu := threeCoupled_chart_analytic r k p
  have he : coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) ∘
      (chartAt ThreeModel p).symm = fun y =>
      (k:ℝ)^2*(((( ((chartAt ThreeModel p).symm y).2:ℂ)^k*productA ((chartAt ThreeModel p).symm y).1^(k-1)).re+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*(r:ℂ)^k*productB ((chartAt ThreeModel p).symm y).1^(k-1)).re)^2+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*productA ((chartAt ThreeModel p).symm y).1^(k-1)).im^2+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*(r:ℂ)^k*productB ((chartAt ThreeModel p).symm y).1^(k-1)).im^2-
        (threeCoupled r k ((chartAt ThreeModel p).symm y))^2+
        (threeCoupledComplex r k ((chartAt ThreeModel p).symm y)).im^2) := by
    funext y; exact threeCoupled_gradient_value r k hk _
  rw [he]
  exact contDiff_const.mul (((((Complex.reCLM.contDiff.comp hα).add
    (Complex.reCLM.contDiff.comp hβ)).pow 2).add ((Complex.imCLM.contDiff.comp hα).pow 2)).add
    ((Complex.imCLM.contDiff.comp hβ).pow 2) |>.sub (hu.pow 2) |>.add ((Complex.imCLM.contDiff.comp hC).pow 2))
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartPairRankTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
lemma threeCoupled_profile_rank_dense {m : ℕ} (hm : 1 ≤ m)
    {O : Set ThreeModel} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x ∈ O, Function.Surjective (fderiv ℝ
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  obtain ⟨x,hx⟩ := threeCoupled_profile_rank_somewhere hm
  exact analytic_rank_dense _ _ (threeCoupled_chart_analytic _ _ _)
    (threeCoupled_gradient_chart_analytic _ _ (by omega) _) hx hO hne
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
lemma threeNormalInv_injective : Function.Injective threeNormalInv := by
  intro x y h
  have hh := congrArg (chartAt ThreeModel threeProfileCenter) h
  dsimp [threeNormalInv,Function.comp_def] at hh
  rw [(chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial),
    (chartAt ThreeModel threeProfileCenter).right_inv (by rw [three_chart_target]; trivial)] at hh
  exact threeNormalEquiv.injective hh

end


open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalInv_isOpenMap : IsOpenMap threeNormalInv := by
  intro U hU
  change IsOpen (((chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv) '' U)
  rw [image_comp]
  exact (chartAt ThreeModel threeProfileCenter).isOpen_image_symm_of_subset_target
    (threeNormalEquiv.toHomeomorph.isOpenMap U hU) (by rw [three_chart_target]; exact subset_univ _)
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
lemma threeNormalInv_mem_closedBall_iff (y : NormalWaveSpace) (r : ℝ) :
    threeNormalInv y ∈ threeNormalInv '' closedBall 0 r ↔ ‖y‖ ≤ r := by
  rw [threeNormalInv_injective.mem_set_image,mem_closedBall,dist_zero_right]
lemma threeNormalInv_mem_ball_iff (y : NormalWaveSpace) (r : ℝ) :
    threeNormalInv y ∈ threeNormalInv '' ball 0 r ↔ ‖y‖ < r := by
  rw [threeNormalInv_injective.mem_set_image,mem_ball,dist_zero_right]
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma threeCollar_isOpen (b c : ℝ) : IsOpen (threeCollar b c) :=
  (threeNormalInv_isOpenMap _ isOpen_ball).sdiff (threeNormalInv_closedBall_closed b)
lemma threeCollar_nonempty {b c : ℝ} (hb : 0<b) (hbc : b < c) : (threeCollar b c).Nonempty := by
  obtain ⟨y,hy⟩ := exists_norm_eq NormalWaveSpace (show 0 ≤ (b+c)/2 by linarith)
  refine ⟨threeNormalInv y,?_,?_⟩
  · rw [threeNormalInv_mem_ball_iff,hy]; linarith
  · rw [threeNormalInv_mem_closedBall_iff,hy]; linarith
lemma three_exterior_profile_pair
    (g : SmoothMetric ThreeModel ThreeManifold) {b : ℝ} (he : ThreeExterior g b)
    (k : ℕ) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q)
    {q : ThreeManifold} (hq : q∉threeNormalInv '' closedBall 0 b) :
    coordinateGradientPair g u u q=coordinateGradientPair threeBackgroundMetric
      (threeCoupled threeCouplingRadius k) (threeCoupled threeCouplingRadius k) q := by
  have hgerm : u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
    filter_upwards [(threeNormalInv_closedBall_closed b).isOpen_compl.mem_nhds hq] with z hz
    exact hu z hz
  rw [coordinateGradientPair_congr_nhds g hgerm]
  exact coordinateGradientPair_metric_point_eq g threeBackgroundMetric q
    (fun v w => congrArg (fun T => T v w) (he q hq)) _ _
lemma three_collar_rank_oai
    (g : SmoothMetric ThreeModel ThreeManifold) {b c : ℝ} (hb : 0<b) (hbc : b < c)
    (he : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q) :
    ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈threeCollar b c ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  let ψ := (chartAt ThreeModel threeProfileCenter).symm
  let O := ψ ⁻¹' threeCollar b c
  have hO : IsOpen O := (threeCollar_isOpen b c).preimage (three_chart_symm_continuous _)
  have hne : O.Nonempty := by
    obtain ⟨q,hq⟩ := threeCollar_nonempty hb hbc
    obtain ⟨y,hy,heq⟩ := hq.1
    exact ⟨threeNormalEquiv y,by simpa only [O,ψ,mem_preimage,←heq,threeNormalInv,Function.comp_apply] using hq⟩
  obtain ⟨x,hx,hrank⟩ := threeCoupled_profile_rank_dense hm hO hne
  refine ⟨x,hx,?_⟩
  have hgerm : (fun y => (u (ψ y),coordinateGradientPair g u u (ψ y))) =ᶠ[𝓝 x]
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) (ψ y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) (ψ y))) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact Prod.ext (hu _ hy.2) (three_exterior_profile_pair g he _ u hu hy.2)
  rw [hgerm.fderiv_eq]
  exact hrank

end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_collar_rank_oai := @OAI.YauCounterexamples.three_collar_rank_oai
