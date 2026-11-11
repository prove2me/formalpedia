-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_parametric_short_lower_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:30:14.004815+00:00
-- url     : https://prove2.me/submissions/d47371d9-df76-434c-b24c-88e51a61cab2

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A027
import Definitions.Def_OAIQ232A028

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ShortSmoothFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma smooth_family_local_inverse {Z : P×E → E} {p : P} {x : E}
    (hZ : ContDiffAt ℝ ∞ Z (p,x))
    (hDx : HasFDerivAt (fun y => Z (p,y)) (ContinuousLinearMap.id ℝ E) x) :
    ∃ B : P×E → E, ContDiffAt ℝ ∞ B (p,Z (p,x)) ∧ B (p,Z (p,x))=x ∧
      (∀ᶠ q in 𝓝 (p,Z (p,x)),Z (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 (p,x), B (q.1,Z q)=q.2) ∧
      (∀ᶠ q : (P×E)×E in 𝓝 ((p,Z (p,x)),x),
        Z (q.1.1,q.2)=q.1.2 ↔ B q.1=q.2) := by
  let F : (P×E)×E → E := fun q => Z (q.1.1,q.2)-q.1.2
  have hF : ContDiffAt ℝ ∞ F ((p,Z (p,x)),x) :=
    (hZ.comp (f := fun q : (P×E)×E => (q.1.1,q.2)) ((p,Z (p,x)),x)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hFy : HasFDerivAt (fun y => F ((p,Z (p,x)),y)) (ContinuousLinearMap.id ℝ E) x :=
    hDx.sub_const (Z (p,x))
  have hpart : fderiv ℝ F ((p,Z (p,x)),x) ∘L inr ℝ (P×E) E=ContinuousLinearMap.id ℝ E := by
    have H := (hF.differentiableAt (by simp)).hasFDerivAt.comp
      (f := fun y => ((p,Z (p,x)),y)) x
      ((hasFDerivAt_const (p,Z (p,x)) x).prodMk (hasFDerivAt_id x))
    exact H.unique hFy
  have hi : (fderiv ℝ F ((p,Z (p,x)),x) ∘L inr ℝ (P×E) E).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  let B := hF.implicitFunction (by simp) hi
  have hB : ContDiffAt ℝ ∞ B (p,Z (p,x)) := hF.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hBx : B (p,Z (p,x))=x := hF.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hiff : ∀ᶠ q : (P×E)×E in 𝓝 ((p,Z (p,x)),x),
      Z (q.1.1,q.2)=q.1.2 ↔ B q.1=q.2 := by
    filter_upwards [hF.eventually_apply_eq_iff_implicitFunction (by simp) hi] with q hq
    simpa only [F,sub_self,sub_eq_zero] using hq
  refine ⟨B,hB,hBx,?_,?_,hiff⟩
  · filter_upwards [hF.eventually_apply_implicitFunction (by simp) hi] with q hq
    simpa only [F,sub_self,sub_eq_zero] using hq
  · have hc : ContinuousAt (fun q : P×E => ((q.1,Z q),q.2)) (p,x) :=
      (continuousAt_fst.prodMk hZ.continuousAt).prodMk continuousAt_snd
    filter_upwards [hc.eventually hiff] with q hq
    exact hq.mp rfl

lemma parametric_smooth_short_action {Z : (P×ℝ)×E → E} {ψ K : P×E → ℝ}
    {p : P} {x : E} (hZ : ContDiffAt ℝ ∞ Z ((p,0),x))
    (hZ0 : ∀ᶠ y in 𝓝 x,Z ((p,0),y)=y)
    (hψ : ContDiffAt ℝ ∞ ψ (p,x)) (hK : ContDiffAt ℝ ∞ K (p,x)) :
    ∃ (B : (P×ℝ)×E → E) (U : (P×ℝ)×E → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),Z (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,Z q)=q.2) ∧
      (∀ q,U q=ψ (q.1.1,B q)+q.1.2*K (q.1.1,B q)) ∧
      Tendsto (fun q : (P×ℝ)×E => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  have hDx : HasFDerivAt (fun y => Z ((p,0),y)) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).congr_of_eventuallyEq hZ0
  obtain ⟨B,hB,hBx,hBZ,hZB,hiff⟩ := smooth_family_local_inverse hZ hDx
  have hx0 := hZ0.self_of_nhds
  rw [hx0] at hB hBx hBZ hiff
  let U : (P×ℝ)×E → ℝ := fun q => ψ (q.1.1,B q)+q.1.2*K (q.1.1,B q)
  have hbq : ContDiffAt ℝ ∞ (fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) :=
    contDiffAt_fst.fst.prodMk hB
  have hU : ContDiffAt ℝ ∞ U ((p,0),x) := by
    have hpψ : ContDiffAt ℝ ∞ ψ (p,B ((p,0),x)) := by rwa [hBx]
    have hpK : ContDiffAt ℝ ∞ K (p,B ((p,0),x)) := by rwa [hBx]
    exact (hpψ.comp (f := fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) hbq).add
      (contDiffAt_fst.snd.mul (hpK.comp (f := fun q : (P×ℝ)×E => (q.1.1,B q)) ((p,0),x) hbq))
  have hU0 : (fun y => U ((p,0),y))=ᶠ[𝓝 x] (fun y => ψ (p,y)) := by
    have hc : ContinuousAt (fun y : E => ((p,(0:ℝ)),y)) x :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.eventually hZB,hZ0] with y hy hz
    rw [hz] at hy
    simp only [U,hy,zero_mul,add_zero]
  refine ⟨B,U,hB,hU,hBx,hBZ,hZB,fun _ => rfl,?_⟩
  have H := (ContDiffAt.partial_snd_fderiv_two (f := fun q y => U (q,y)) hU).continuousAt.tendsto
  rwa [hU0.fderiv.fderiv_eq] at H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma coordinateBackward_contMDiffAt {a : M} {q : ℝ × Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.2.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,ℝ × Model n × (Model n →L[ℝ] ℝ)) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.2.1 hg
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hv := (contDiffAt_fst.neg.smul ((hi.comp q hz).clm_apply hl))
  exact (movingNormal_contMDiffAt hq).comp q (hz.prodMk hv).contMDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartGradientVector_total_eq {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,chartGradientVector a q.1 q.2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) =
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm
        (q.1,(riemannianCoordinateMetric a q.1).inverse q.2) := by
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm q.1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hq
  dsimp only [chartGradientVector]
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateRaise_contDiffAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.1 hg
  exact contDiffAt_fst.prodMk ((hi.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartGradientVector_total_continuousAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContinuousAt (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,chartGradientVector a q.1 q.2⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)) q := by
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  let f := fun q : Model n×(Model n →L[ℝ] ℝ) =>
    (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)
  have hT : f q∈c.target := (tangent_chart_target_iff _ (f q)).mpr hq
  have hc : ContinuousAt c.symm (f q) :=
    (continuousOn_extChartAt_symm _).continuousAt ((isOpen_extChartAt_target _).mem_nhds hT)
  have hf : ContinuousAt f q := (coordinateRaise_contDiffAt hq).continuousAt
  apply (hc.comp (x := q) hf).congr_of_eventuallyEq
  have he : ∀ᶠ q' : Model n×(Model n →L[ℝ] ℝ) in 𝓝 q,
      q'.1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hq)
  filter_upwards [he] with q' hq'
  exact chartGradientVector_total_eq hq'

omit [Nonempty M] in
lemma chartGradientVector_regular_near {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.1 q.2∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1)) :
    ∀ᶠ q' : Model n×(Model n →L[ℝ] ℝ) in 𝓝 q,
      chartGradientVector a q'.1 q'.2∈injectivityDomain
        ((extChartAt 𝓘(ℝ,Model n) a).symm q'.1) :=
  (chartGradientVector_total_continuousAt hq).preimage_mem_nhds
    (isOpen_total_injectivityDomain.mem_nhds hp)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LiftedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma cost_minimizingVector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : cost x (riemannianExp x p)=‖p‖^2/2 := by
  unfold cost
  rw [show dist x (riemannianExp x p)=‖p‖ from hp]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ShortForward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma shortEnergy_eq_norm {a : M} {y : Model n}
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).target) (ψ : Model n → ℝ) :
    shortEnergy a ψ y=‖chartGradientVector a y (fderiv ℝ ψ y)‖^2/2 := by
  have H := (riemannianCoordinateMetric_isInvertible hy).self_apply_inverse (fderiv ℝ ψ y)
  have He := congrArg (fun L : Model n →L[ℝ] ℝ =>
    L ((riemannianCoordinateMetric a y).inverse (fderiv ℝ ψ y))) H
  rw [riemannianCoordinateMetric_apply,real_inner_self_eq_norm_sq] at He
  exact congrArg (fun t : ℝ => t/2) He.symm

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma shortForward_zero {a : M} {ψ : Model n → ℝ} {y : Model n}
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).target) : shortForward a ψ (0,y)=y := by
  simp only [shortForward,zero_smul,coordinateBackward,map_zero,smul_zero]
  rw [movingNormal_zero hy,(extChartAt 𝓘(ℝ,Model n) a).right_inv hy]

omit [Nonempty M] in
lemma shortForward_action {a : M} {ψ : Model n → ℝ} {q : ℝ×Model n}
    (hq : q.2∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.2 (q.1 • fderiv ℝ ψ q.2)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)) :
    cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)
      (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2))=q.1^2*shortEnergy a ψ q.2 ∧
    HasFDerivAt (chartCost a (coordinateBackward a (-1,q.2,q.1 • fderiv ℝ ψ q.2)))
      (-(q.1 • fderiv ℝ ψ q.2)) q.2 := by
  refine ⟨?_,chartCost_gradient_at_contact hq hp⟩
  rw [coordinateBackward_eq_exp_chartGradient hq,
    cost_minimizingVector (injectivityDomain_subset_minimizingVectors _ hp),shortEnergy_eq_norm hq]
  simp only [chartGradientVector,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [CompleteSpace P] in
lemma parametricShortEnergy_contDiffAt {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ContDiffAt ℝ ∞ (parametricShortEnergy a ψ) (p,x) := by
  have hD := ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ
  have hg := ((contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hx)).comp (f := Prod.snd) (p,x) contDiffAt_snd
  have hi := (riemannianCoordinateMetric_isInvertible hx).contDiffAt_map_inverse.comp
    (f := fun q : P×Model n => riemannianCoordinateMetric a q.2) (p,x) hg
  exact (hD.clm_apply (hi.clm_apply hD)).div_const 2

omit [Nonempty M] [CompleteSpace P] in
lemma parametricShortForward_contDiffAt {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ContDiffAt ℝ ∞ (parametricShortForward a ψ) ((p,0),x) := by
  have hD := ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ
  let A : (P×ℝ)×Model n → (ℝ×Model n×(Model n →L[ℝ] ℝ)) := fun q =>
    (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)
  have hA : ContDiffAt ℝ ∞ A ((p,0),x) :=
    contDiffAt_const.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_fst.snd.smul (hD.comp (f := fun q : (P×ℝ)×Model n => (q.1.1,q.2))
        ((p,0),x) (contDiffAt_fst.fst.prodMk contDiffAt_snd))))
  have hC : ContMDiffAt 𝓘(ℝ,(P×ℝ)×Model n) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a ∘ A) ((p,0),x) :=
    (coordinateBackward_contMDiffAt (q := A ((p,0),x)) hx).comp
      (f := A) ((p,0),x) hA.contMDiffAt
  have he : coordinateBackward a (A ((p,0),x))=(extChartAt 𝓘(ℝ,Model n) a).symm x := by
    simp only [A,coordinateBackward,zero_smul,map_zero,smul_zero,movingNormal_zero hx]
  have hc : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ (extChartAt 𝓘(ℝ,Model n) a)
      (coordinateBackward a (A ((p,0),x))) := by
    rw [he]
    exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hx)
  exact (hc.comp (f := coordinateBackward a ∘ A) ((p,0),x) hC).contDiffAt

omit [Nonempty M] [CompleteSpace P] in
lemma parametricShortForward_regular_near {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∀ᶠ q : (P×ℝ)×Model n in 𝓝 ((p,0),x),
      q.2∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      chartGradientVector a q.2 (q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) ∧
      coordinateBackward a (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        (extChartAt 𝓘(ℝ,Model n) a).source := by
  have hD := (ContDiffAt.partial_snd_fderiv (f := fun p y => ψ (p,y)) hψ).continuousAt
  let A : (P×ℝ)×Model n → Model n×(Model n →L[ℝ] ℝ) := fun q =>
    (q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)
  have hA : ContinuousAt A ((p,0),x) := continuousAt_snd.prodMk
    (continuousAt_fst.snd.smul (hD.comp (x := ((p,0),x))
      (continuousAt_fst.fst.prodMk continuousAt_snd)))
  have hp : chartGradientVector a (A ((p,0),x)).1 (A ((p,0),x)).2∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm x) := by
    simpa only [A,chartGradientVector,zero_smul,map_zero] using zero_mem_injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm x)
  have ha := hA.eventually (chartGradientVector_regular_near hx hp)
  have hs : ∀ᶠ q : (P×ℝ)×Model n in 𝓝 ((p,0),x),
      q.2∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := ((coordinateBackward_contMDiffAt (q := (-1,A ((p,0),x))) hx).continuousAt.comp
    (x := ((p,0),x)) (continuousAt_const.prodMk hA))
  have he : coordinateBackward a (-1,A ((p,0),x))=(extChartAt 𝓘(ℝ,Model n) a).symm x := by
    simp only [A,coordinateBackward,zero_smul,map_zero,smul_zero,movingNormal_zero hx]
  have hb := hc.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds
    (he.symm ▸ (extChartAt 𝓘(ℝ,Model n) a).map_target hx))
  exact hs.and (ha.and hb)

omit [Nonempty M] in
lemma geometric_parametric_short_family {a : M} {ψ : P×Model n → ℝ} {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ (B : (P×ℝ)×Model n → Model n) (U : (P×ℝ)×Model n → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),parametricShortForward a ψ (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2) ∧
      (∀ q,U q=ψ (q.1.1,B q)+q.1.2*parametricShortEnergy a ψ (q.1.1,B q)) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  apply parametric_smooth_short_action (parametricShortForward_contDiffAt hx hψ) _ hψ
    (parametricShortEnergy_contDiffAt hx hψ)
  filter_upwards [(isOpen_extChartAt_target a).mem_nhds hx] with y hy
  exact shortForward_zero hy

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ShortPoleIdentities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] [CompleteSpace P] in
lemma short_family_first_jet_limit {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} {B : (P×ℝ)×Model n → Model n} {U : (P×ℝ)×Model n → ℝ}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hU : ContDiffAt ℝ ∞ U ((p,0),x))
    (hZB : ∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2)
    (hUE : ∀ q,U q=ψ (q.1.1,B q)+q.1.2*parametricShortEnergy a ψ (q.1.1,B q)) :
    Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fun w => U (q.1,w)) q.2)
      (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fun w => ψ (p,w)) x)) := by
  have hi : ContinuousAt (fun w : Model n => ((p,(0:ℝ)),w)) x :=
    continuousAt_const.prodMk continuousAt_id
  have hz := hi.eventually hZB
  have heq : (fun w => U ((p,0),w))=ᶠ[𝓝 x] (fun w => ψ (p,w)) := by
    filter_upwards [hz,(isOpen_extChartAt_target a).mem_nhds hx] with w hw hwc
    change B ((p,0),shortForward a (fun v => ψ (p,v)) (0,w))=w at hw
    rw [shortForward_zero hwc] at hw
    rw [hUE,hw]
    simp only [zero_mul,add_zero]
  have H := (ContDiffAt.partial_snd_fderiv (f := fun q w => U (q,w)) hU).continuousAt.tendsto
  rw [heq.fderiv_eq] at H
  exact H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_HopfApproximation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma hopfLax_le_self {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
    hopfLax t u z ≤ u z := by
  simpa only [cost,dist_self,zero_pow (by norm_num : 2≠0),zero_div,add_zero] using hopfLax_le hu t z z

lemma hopfLax_minimizer_distance {u : M → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {t : ℝ} (ht : 0<t) {z x : M}
    (hx : hopfLax t u z=u x+cost x z/t) : dist x z ≤ 2*(L:ℝ)*t := by
  have H := hopfLax_le_self hu.continuous t z
  rw [hx,cost] at H
  have Hl := (abs_le.mp (show |u x-u z| ≤ (L:ℝ)*dist x z by
    simpa only [Real.dist_eq] using hu.dist_le_mul x z)).1
  have HH : dist x z^2/2 ≤ (u z-u x)*t := by
    apply (div_le_iff₀ ht).mp
    linarith only [H]
  by_contra h
  have hq : 0 < dist x z := (by positivity : 0 ≤ 2*(L:ℝ)*t).trans_lt (lt_of_not_ge h)
  have Hl' := mul_le_mul_of_nonneg_right (show u z-u x ≤ (L:ℝ)*dist x z by linarith only [Hl]) ht.le
  nlinarith only [HH,Hl',mul_pos hq (sub_pos.mpr (lt_of_not_ge h))]

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma uniform_hopfLax_minimizers_eventually_in (L : ℝ≥0) {x : M} {V : Set M}
    (hV : V∈𝓝 x) :
    ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x), 0<q.1 → ∀ f : M → ℝ, LipschitzWith L f →
      ∀ y : M, hopfLax q.1 f q.2=f y+cost y q.2/q.1 → y∈V := by
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hc : ContinuousAt (fun q : ℝ×M => 2*(L:ℝ)*q.1+dist q.2 x) (0,x) := by fun_prop
  have he : ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x),2*(L:ℝ)*q.1+dist q.2 x < r :=
    hc.eventually_lt continuousAt_const (by simpa only [mul_zero,dist_self,zero_add] using hr)
  filter_upwards [he] with q hq
  intro ht f hf y hy
  apply hrV
  change dist y x < r
  have hd := hopfLax_minimizer_distance hf ht hy
  have htri := dist_triangle y q.2 x
  linarith only [hd,htri,hq]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ShortLocalMinimum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartCost_pair_contDiffAt_diagonal {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×Model n =>
      chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2) (x,x) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm x :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm x,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    (zero_mem_injectivityDomain (n := n) (χ.symm x))
  simp only [riemannianExp_zero] at hc
  exact (hc.comp (x,x) ((hi.comp (x,x) contDiffAt_snd.contMDiffAt).prodMk
    (hi.comp (x,x) contDiffAt_fst.contMDiffAt))).contDiffAt
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_⟩
  have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (continuousAt_extChartAt y).eventually
      ((e.open_target.mem_nhds (hep ▸ e.map_source hpe)))
  have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
    (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
  have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
    have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
      rw [hLy]; exact extChartAt_source_mem_nhds y)
    exact H
  filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
  apply d.injOn hzs hsz
  have HR := e.right_inv hzt
  rw [he] at HR
  exact HR

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_chart_fiber_log {x a : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x)
    (ha : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let ψ := extChartAt 𝓘(ℝ,Model n) a
    let u := ψ (riemannianExp x p)
    ∃ e : Model n → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ e u ∧ e u=p ∧
      (∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w) ∧
      Function.Injective (fderiv ℝ e u) := by
  let ψ := extChartAt 𝓘(ℝ,Model n) a
  let u := ψ (riemannianExp x p)
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hu : u∈ψ.target := ψ.map_source ha
  have hui : ψ.symm u=riemannianExp x p := ψ.left_inv ha
  obtain ⟨L,hL,hLp,hLi⟩ := exists_smooth_fiber_log hp
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ.symm u :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hu)
  let e := fun w : Model n => L (ψ.symm w)
  have he : ContDiffAt ℝ ∞ e u :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (ψ.symm u) from by
      simpa only [hui] using hL).comp u hi).contDiffAt
  have heu : e u=p := by dsimp [e]; rw [hui]; exact hLp
  have hei : ∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w :=
    hi.continuousAt.eventually (by simpa only [hui] using hLi)
  refine ⟨e,he,heu,hei,?_⟩
  let c : V → Model n := fun v => ψ (riemannianExp x v)
  have hc : ContDiffAt ℝ ∞ c p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using ha)).comp p
        (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hid : (fun w => c (e w)) =ᶠ[𝓝 u] (fun w => w) := by
    filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds hu] with w hw hwt
    dsimp [c]
    rw [hw,ψ.right_inv hwt]
  have HD := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp u (by simpa only [heu] using hc.differentiableAt (by simp))
    (he.differentiableAt (by simp)),fderiv_fun_id] at HD
  intro v w hvw
  change fderiv ℝ e u v=fderiv ℝ e u w at hvw
  have H := congrArg (fun C : Model n →L[ℝ] Model n => C v-C w) HD
  apply sub_eq_zero.mp
  simpa only [ContinuousLinearMap.comp_apply,hvw,sub_self,ContinuousLinearMap.id_apply] using H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

lemma exists_norm_sq_lower_of_injective (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ c>0, ∀ v:E, c*‖v‖^2 ≤ ‖L v‖^2 := by
  obtain ⟨K,hK,HK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hKr),?_⟩
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz L HK v
  have H2 := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg K.coe_nonneg (norm_nonneg (L v)))).mpr H
  rw [mul_pow] at H2
  have HH : ‖v‖^2/(K:ℝ)^2 ≤ ‖L v‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hKr)).mpr (by simpa only [mul_comm] using H2)
  simpa only [div_eq_mul_inv,mul_comm] using HH

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_DiagonalCostConvexity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartCost_diagonal_coercive {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ∃ m>0, ∀ d : Model n, m*‖d‖^2 ≤
      fderiv ℝ (fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z))) z d d := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let x := χ.symm z
  have hx : x∈χ.source := χ.map_target hz
  have hxz : χ x=z := χ.right_inv hz
  change extChartAt 𝓘(ℝ,Model n) a x=z at hxz
  have hp := zero_mem_injectivityDomain (n := n) x
  obtain ⟨e,he,he0,hei,hinj⟩ := exists_smooth_chart_fiber_log hp
    (show riemannianExp x 0∈χ.source from by rwa [riemannianExp_zero])
  simp only [riemannianExp_zero,hxz] at he he0 hei hinj
  obtain ⟨m,hm,hbound⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hinj
  refine ⟨m,hm,fun d => ?_⟩
  have hC : ContDiffAt ℝ 2 (normalCost (n := n) x 0) 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hzero : fderiv ℝ (normalCost (n := n) x 0) 0=0 := by
    rw [(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [neg_zero,map_zero]
  have heq : chartCost a x =ᶠ[𝓝 z] (fun w => normalCost (n := n) x 0 (e w)) := by
    filter_upwards [hei] with w hw
    simp only [normalCost,riemannianExp_zero,hw,chartCost]
  rw [heq.fderiv.fderiv_eq]
  have H := second_fderiv_comp_stationary (f := normalCost (n := n) x 0) (g := e)
    (he0.symm ▸ hC) (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (by rwa [he0]) d d
  rw [H,he0]
  change m*‖d‖^2 ≤ normalHessian x 0 (fderiv ℝ e z d) (fderiv ℝ e z d)
  rw [←hessianValue_eq_normalHessian hp,hessianValue_zero]
  exact hbound d

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LocalMountains
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y]

lemma lower_support_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S, ∀ d : E, 0 ≤ fderiv ℝ (fderiv ℝ f) z d d)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    f x+fderiv ℝ f x (y-x) ≤ f y := by
  let d := y-x
  let l : ℝ → E := fun t => x+t • d
  let g : ℝ → ℝ := fun t => f (l t)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (l t) d
  let g'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (l t) d d
  have hl : ∀ t∈Icc (0:ℝ) 1, l t∈S := by
    intro t ht
    have H := hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [l,d]
    module
  have hld (t : ℝ) : HasDerivAt l d t := by
    simpa only [l,id_eq,one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t :=
    ((hf (l t) (hl t ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
  have hg' (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g' (g'' t) t := by
    have H := (((hf (l t) (hl t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
    simpa only [g',g'',Function.comp_apply,map_zero,add_zero] using H.clm_apply (hasDerivAt_const t d)
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hH _ (hl t (interior_subset ht)) d)
  have H := hconv.deriv_le_slope (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_lt_one (hg 0 (by constructor <;> norm_num)).differentiableAt
  rw [(hg 0 (by constructor <;> norm_num)).deriv] at H
  simp only [g,g',l,d,zero_smul,add_zero,one_smul,add_sub_cancel,slope,
    sub_zero,inv_one,one_smul,vsub_eq_sub] at H
  linarith

lemma bilinear_nonnegative_of_norm_sub_le {B H : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hB : ∀ d, m*‖d‖^2 ≤ B d d) (hH : ‖H-B‖≤ m) (d : E) : 0≤H d d := by
  have hn := (H-B).le_opNorm₂ d d
  have hmul := mul_le_mul_of_nonneg_right hH (sq_nonneg ‖d‖)
  have hdiff : H d d-B d d ≤ ‖(H-B) d d‖ := le_abs_self _
  have hdiff' : -(H d d-B d d) ≤ ‖(H-B) d d‖ := neg_le_abs _
  have he : ‖H-B‖*‖d‖*‖d‖=‖H-B‖*‖d‖^2 := by ring
  rw [he] at hn
  have H' := hB d
  nlinarith

lemma exists_local_mountains {F : Y → E → ℝ} {x : E} {y : Y} {m : ℝ}
    (hm : 0< m)
    (hC : ContinuousAt (fun q : E×Y => fderiv ℝ (fderiv ℝ (F q.2)) q.1) (x,y))
    (hD : ∀ᶠ q : E×Y in 𝓝 (x,y), ContDiffAt ℝ 2 (F q.2) q.1)
    (hpos : ∀ d:E, m*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ (F y)) x d d) :
    ∃ r>0, ∃ V∈𝓝 y, ∀ y'∈V, ∀ z∈Metric.closedBall x r,
      fderiv ℝ (F y') z=0 → ∀ w∈Metric.closedBall x r, F y' z≤F y' w := by
  have H := @ContinuousAt.norm (E×Y) (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _
    (hC.sub (continuousAt_const (y := fderiv ℝ (fderiv ℝ (F y)) x)))
  have Hn : ∀ᶠ q : E×Y in 𝓝 (x,y),
      ‖fderiv ℝ (fderiv ℝ (F q.2)) q.1-fderiv ℝ (fderiv ℝ (F y)) x‖< m := by
    apply H.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero] using hm
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp (Hn.and hD)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨r,hr,V,hV,?_⟩
  intro y' hy' z hz hs w hw
  have Hlow := lower_support_of_nonnegative_hessian (f := F y') (convex_closedBall x r)
    (fun u hu => (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).2)
    (fun u hu d => bilinear_nonnegative_of_norm_sub_le hpos
      (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).1.le d) hz hw
  simpa only [hs,zero_apply,add_zero] using Hlow

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UniformShortMinima
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [Nonempty M] in
lemma exists_parametric_short_action_local_minima {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ r>0, ∃ V∈𝓝 ((p,(0:ℝ)),x), ∀ q∈V, ∀ y∈Metric.closedBall x r,
      fderiv ℝ (fun w => q.1.2*ψ (q.1.1,w)+
        chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) w) y=0 →
      ∀ w∈Metric.closedBall x r, q.1.2*ψ (q.1.1,y)+
        chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) y≤
          q.1.2*ψ (q.1.1,w)+chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) w := by
  let F : ((P×ℝ)×Model n) → Model n → ℝ := fun q y =>
    q.1.2*ψ (q.1.1,y)+chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) y
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (((p,(0:ℝ)),x),x) :=
    (contDiffAt_fst.fst.snd.mul (hψ.comp (f := fun q : ((P×ℝ)×Model n)×Model n => (q.1.1.1,q.2)) _
      (contDiffAt_fst.fst.fst.prodMk contDiffAt_snd))).add
      ((chartCost_pair_contDiffAt_diagonal (a := a) (x := x) hx).comp (((p,(0:ℝ)),x),x)
        (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hswap : ContinuousAt (fun q : Model n×((P×ℝ)×Model n) => q.swap) (x,((p,(0:ℝ)),x)) :=
    continuousAt_snd.prodMk continuousAt_fst
  have hH : ContinuousAt (fun q : Model n×((P×ℝ)×Model n) =>
      fderiv ℝ (fderiv ℝ (F q.2)) q.1) (x,((p,(0:ℝ)),x)) := by
    have H := (ContDiffAt.partial_snd_fderiv_two (f := F) hF).continuousAt.comp
      (x := (x,((p,(0:ℝ)),x))) hswap
    exact H
  have hD : ∀ᶠ q : Model n×((P×ℝ)×Model n) in 𝓝 (x,((p,(0:ℝ)),x)),
      ContDiffAt ℝ 2 (F q.2) q.1 := by
    have H := hswap.eventually ((hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    filter_upwards [H] with q hq
    exact hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨m,hm,hpos⟩ := chartCost_diagonal_coercive hx
  have heq : F ((p,0),x)=chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm x) := by
    ext y; simp only [F,zero_mul,zero_add]
  have hposF : ∀ d, m*‖d‖^2≤fderiv ℝ (fderiv ℝ (F ((p,0),x))) x d d := by
    rw [heq]
    exact hpos
  exact exists_local_mountains hm hH hD hposF

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ParametricShortLowerJets
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_parametric_short_lower_jets {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x)) :
    ∃ r>0, ∃ (B : (P×ℝ)×Model n → Model n) (U : (P×ℝ)×Model n → ℝ),
      ContDiffAt ℝ ∞ B ((p,0),x) ∧ ContDiffAt ℝ ∞ U ((p,0),x) ∧ B ((p,0),x)=x ∧
      (∀ᶠ q in 𝓝 ((p,0),x),parametricShortForward a ψ (q.1,B q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2) ∧
      (∀ᶠ q in 𝓝 ((p,0),x),0<q.1.2 → ∀ f : M → ℝ, LipschitzWith L f →
        (∀ w∈Metric.closedBall x r,ψ (q.1.1,w)≤f ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
        U q≤hopfLax q.1.2 f ((extChartAt 𝓘(ℝ,Model n) a).symm q.2) ∧
        (f ((extChartAt 𝓘(ℝ,Model n) a).symm (B q))=ψ (q.1.1,B q) →
          U q=hopfLax q.1.2 f ((extChartAt 𝓘(ℝ,Model n) a).symm q.2))) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fun y => U (q.1,y)) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fun y => ψ (p,y)) x)) ∧
      Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fderiv ℝ (fun y => U (q.1,y))) q.2)
        (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fderiv ℝ (fun y => ψ (p,y))) x)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨B,U,hB,hU,hBx,hBZ,hZB,hUE,hUH⟩ := geometric_parametric_short_family hx hψ
  obtain ⟨r,hr,V,hV,hmin⟩ := exists_parametric_short_action_local_minima hx hψ
  have hBmap : ContinuousAt (fun q : (P×ℝ)×Model n => (q.1,B q)) ((p,0),x) :=
    continuousAt_fst.prodMk hB.continuousAt
  have hBreg := hBmap.eventually (show ∀ᶠ q in 𝓝 ((p,0),B ((p,0),x)),
      q.2∈χ.target ∧ chartGradientVector a q.2 (q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈
        injectivityDomain (χ.symm q.2) ∧
      coordinateBackward a (-1,q.2,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) q.2)∈χ.source by
    rw [hBx]; exact parametricShortForward_regular_near hx hψ)
  have hPsib : ∀ᶠ q in 𝓝 ((p,(0:ℝ)),x), ContDiffAt ℝ 1 (fun y => ψ (q.1.1,y)) (B q) := by
    have hc : ContinuousAt (fun q : (P×ℝ)×Model n => (q.1.1,B q)) ((p,0),x) :=
      continuousAt_fst.fst.prodMk hB.continuousAt
    have H := hc.eventually (show ∀ᶠ v in 𝓝 (p,B ((p,0),x)),ContDiffAt ℝ 1 ψ v by
      rw [hBx]; exact (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    filter_upwards [H] with q hq
    exact hq.comp (B q) (contDiffAt_const.prodMk contDiffAt_id)
  have hBr : ∀ᶠ q in 𝓝 ((p,(0:ℝ)),x), B q∈Metric.closedBall x r := by
    have H := hB.continuousAt.preimage_mem_nhds (show Metric.ball x r∈𝓝 (B ((p,0),x)) by
      rw [hBx]; exact Metric.ball_mem_nhds x hr)
    exact Filter.Eventually.mono H fun _ hy => Metric.ball_subset_closedBall hy
  have hcx : χ.symm x∈χ.source := χ.map_target hx
  have hcm : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ (χ.symm x) :=
    contMDiffAt_extChartAt' (by simpa only [χ,extChartAt_source] using hcx)
  have hWM : χ.source ∩ χ ⁻¹' Metric.ball x r∈𝓝 (χ.symm x) :=
    Filter.inter_mem ((isOpen_extChartAt_source a).mem_nhds hcx)
      (hcm.continuousAt.preimage_mem_nhds (by rw [χ.right_inv hx]; exact Metric.ball_mem_nhds x hr))
  have hi : ContinuousAt χ.symm x := continuousAt_extChartAt_symm'' hx
  have hloc := (continuousAt_fst.snd.prodMk (hi.comp (x := ((p,(0:ℝ)),x)) continuousAt_snd)).eventually
    (uniform_hopfLax_minimizers_eventually_in L hWM)
  refine ⟨r,hr,B,U,hB,hU,hBx,hBZ,hZB,?_,short_family_first_jet_limit hx hU hZB hUE,hUH⟩
  filter_upwards [hBreg,hPsib,hBr,hloc,hBZ,hV] with q hreg hps hbr hlocq hz hq
  intro ht f hf hs
  have he : coordinateBackward a (-1,B q,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) (B q))=χ.symm q.2 := by
    calc
      _=χ.symm (χ (coordinateBackward a (-1,B q,q.1.2 • fderiv ℝ (fun y => ψ (q.1.1,y)) (B q)))) :=
        (χ.left_inv hreg.2.2).symm
      _=χ.symm q.2 := congrArg χ.symm hz
  obtain ⟨ha,hd⟩ := shortForward_action (a := a) (ψ := fun y => ψ (q.1.1,y))
    (q := (q.1.2,B q)) hreg.1 hreg.2.1
  rw [he] at ha hd
  have hstat : fderiv ℝ (fun w => q.1.2*ψ (q.1.1,w)+chartCost a (χ.symm q.2) w) (B q)=0 := by
    have H := ((hps.differentiableAt (by simp)).hasFDerivAt.const_mul q.1.2).add hd
    convert! H.fderiv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [add_neg_cancel]
  have heU : U q=ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)/q.1.2 := by
    rw [hUE,ha]
    dsimp only [parametricShortEnergy]
    congr 1
    field_simp
  have hlo : U q≤hopfLax q.1.2 f (χ.symm q.2) := by
    obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hf.continuous q.1.2 (χ.symm q.2)
    obtain ⟨hys,hyw⟩ := hlocq ht f hf y hy
    have hh := hmin q hq (B q) hbr hstat (χ y) (Metric.ball_subset_closedBall hyw)
    have hyy : χ.symm (χ y)=y := χ.left_inv hys
    have hysup := hs (χ y) (Metric.ball_subset_closedBall hyw)
    change q.1.2*ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)≤
      q.1.2*ψ (q.1.1,χ y)+cost (χ.symm (χ y)) (χ.symm q.2) at hh
    rw [hyy] at hh hysup
    rw [heU,hy]
    apply (mul_le_mul_iff_left₀ ht).mp
    have hd1 : (ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2)/q.1.2)*q.1.2=
        q.1.2*ψ (q.1.1,B q)+cost (χ.symm (B q)) (χ.symm q.2) := by field_simp
    have hd2 : (f y+cost y (χ.symm q.2)/q.1.2)*q.1.2=q.1.2*f y+cost y (χ.symm q.2) := by field_simp
    rw [hd1,hd2]
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hysup ht.le) le_rfl)
  refine ⟨hlo,fun hc => hlo.antisymm ?_⟩
  rw [heU,←hc]
  exact hopfLax_le hf.continuous q.1.2 (χ.symm q.2) (χ.symm (B q))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ParametricLowerSequence
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_parametric_short_lower_sequence_oai {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i)) :
    let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
    ∃ U : ℕ → Model n → ℝ,
      (∀ᶠ i in atTop,ContDiffAt ℝ 2 (U i) (z i) ∧
        U i (z i)=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (z i)) ∧
        ∀ᶠ w in 𝓝 (z i),U i w≤hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      Tendsto (fun i=>fderiv ℝ (U i) (z i)) atTop
        (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) ∧
      Tendsto (fun i=>fderiv ℝ (fderiv ℝ (U i)) (z i)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x)) := by
  dsimp only
  let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
  have hQ := (hp.prodMk_nhds ht).prodMk_nhds hxx
  have hzero : parametricShortForward a ψ ((p,0),x)=x := shortForward_zero hx
  have hz : Tendsto z atTop (𝓝 x) := by
    have H := (parametricShortForward_contDiffAt hx hψ).continuousAt.tendsto.comp hQ
    rwa [hzero] at H
  have hQz := (hp.prodMk_nhds ht).prodMk_nhds hz
  obtain ⟨r,hr,B,U,hB,hU,hBx,hBZ,hZB,hlo,hD,hH⟩ :=
    exists_parametric_short_lower_jets L hx hψ
  obtain ⟨V,hV,hVo,hV0⟩ := mem_nhds_iff.mp hlo
  have hVB := hQz.eventually (hVo.mem_nhds hV0)
  have hBK : ∀ᶠ i in atTop,B ((pj i,tj i),z i)=xj i := hQ.eventually hZB
  have hUC : ∀ᶠ i in atTop,ContDiffAt ℝ 2 U ((pj i,tj i),z i) :=
    hQz.eventually ((hU.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by norm_num))
  refine ⟨fun i w=>U ((pj i,tj i),w),?_,hD.comp hQz,hH.comp hQz⟩
  filter_upwards [hVB,hBK,hUC,htpos,hlip,hbelow,htouch] with i hVi hBi hUi hti hfi hbei hti'
  have htU := hUi.comp (z i) (contDiffAt_const.prodMk contDiffAt_id)
  have H := hV hVi hti (f i) hfi (fun w _=>hbei w)
  have Heq : f i ((extChartAt 𝓘(ℝ,Model n) a).symm (B ((pj i,tj i),z i)))=
      ψ (pj i,B ((pj i,tj i),z i)) := by rw [hBi]; exact hti'
  refine ⟨htU,H.2 Heq,?_⟩
  have hc : ContinuousAt (fun w:Model n=>((pj i,tj i),w)) (z i) :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hc.eventually (hVo.mem_nhds hVi)] with w hw
  exact (hV hw hti (f i) hfi (fun w _=>hbei w)).1

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWTransport.exists_parametric_short_lower_sequence_oai.{u_1, u_2} := @OAI.WeakMTWTransport.exists_parametric_short_lower_sequence_oai.{u_1, u_2}
