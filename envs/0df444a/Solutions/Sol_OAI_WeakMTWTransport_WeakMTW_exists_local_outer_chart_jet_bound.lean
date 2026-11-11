-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:00.686843+00:00
-- url     : https://prove2.me/submissions/35a4cc55-702b-44fe-abcb-f3a9d8c6b103

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_locally_uniform_test_det_bound

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma half_norm_sq_hasFDerivAt (p : E) :
    HasFDerivAt (fun v : E => ‖v‖^2/2) (innerSL ℝ p) p := by
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_smul (1/2:ℝ)
  convert! H using 1
  · ext v; simp only [Pi.smul_apply,smul_eq_mul,id_eq] <;> ring
  · ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      smul_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
    ring

lemma half_norm_sq_fderiv :
    fderiv ℝ (fun v : E => ‖v‖^2/2) = innerSL ℝ := by
  funext p
  exact (half_norm_sq_hasFDerivAt p).fderiv

lemma half_norm_sq_second_fderiv (p a d : E) :
    fderiv ℝ (fderiv ℝ (fun v : E => ‖v‖^2/2)) p a d=inner ℝ a d := by
  rw [half_norm_sq_fderiv]
  rw [(innerSL ℝ).hasFDerivAt.fderiv]
  rfl

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondFderivScalarComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun h => φ (f h))) x ξ ξ =
      iteratedDeriv 2 φ (f x)*(fderiv ℝ f x ξ)^2+
        deriv φ (f x)*fderiv ℝ (fderiv ℝ f) x ξ ξ := by
  let g := fun t : ℝ => f (x+t • ξ)
  have hg : ContDiffAt ℝ 2 g 0 := by
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ => x+t • ξ) 0
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • ξ) from by simpa using hf).comp (0:ℝ)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hg0 : g 0=f x := by simp [g]
  have hline : HasDerivAt (fun t : ℝ => x+t • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const ξ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd : deriv g 0=fderiv ℝ f x ξ := by
    simpa only [Function.comp_def,g,zero_smul,add_zero] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • ξ) from by
        simpa only [zero_smul,add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline).deriv
  have H := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (g 0) from hg0.symm ▸ hφ) hg
  rw [hg0,hd,show iteratedDeriv 2 g 0=fderiv ℝ (fderiv ℝ f) x ξ ξ from
    iteratedDeriv_two_affine_line hf ξ] at H
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x ξ ξ = _
  rw [←iteratedDeriv_two_affine_line (hφ.comp x hf) ξ]
  exact H

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarInverseJet
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

lemma exists_scalar_inverse_jet {φ : ℝ → ℝ} {v l : ℝ}
    (hφ : ContDiffAt ℝ 2 φ v) (hd : HasDerivAt φ l v) (hl : l≠0) :
    ∃ i : ℝ → ℝ, ContDiffAt ℝ 2 i (φ v) ∧ i (φ v)=v ∧
      HasDerivAt i l⁻¹ (φ v) ∧
      (∀ᶠ w in 𝓝 (φ v),φ (i w)=w) ∧
      iteratedDeriv 2 i (φ v)= -iteratedDeriv 2 φ v/l^3 := by
  let i := hφ.localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hi : ContDiffAt ℝ 2 i (φ v) := hφ.to_localInverse (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hiv : i (φ v)=v := hφ.localInverse_apply_image (hd.hasFDerivAt_equiv hl) (by norm_num)
  have hr : ∀ᶠ w in 𝓝 (φ v),φ (i w)=w :=
    (hφ.hasStrictFDerivAt' (hd.hasFDerivAt_equiv hl) (by norm_num)).eventually_right_inverse
  have hiD : HasDerivAt i l⁻¹ (φ v) := (show HasDerivAt φ l (i (φ v)) from hiv.symm ▸ hd).of_local_left_inverse hi.continuousAt hl (by
    simpa only [hiv] using hr)
  refine ⟨i,hi,hiv,hiD,hr,?_⟩
  have hsecond := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (i (φ v)) from hiv.symm ▸ hφ) hi
  have hid : iteratedDeriv 2 (φ ∘ i) (φ v)=0 := by
    have H : (φ ∘ i)=ᶠ[𝓝 (φ v)] (fun w : ℝ => w) := hr
    have H2 := H.deriv.deriv_eq
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id'',deriv_const] using H2
  rw [hid,hiv,hd.deriv,hiD.deriv] at hsecond
  apply (eq_div_iff (pow_ne_zero 3 hl)).mpr
  field_simp at hsecond
  nlinarith only [hsecond]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalar_inverse_lower_test {φ : ℝ → ℝ} (hmono : StrictMono φ)
    {v F : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ (v x))
    {l : ℝ} (hd : HasDerivAt φ l (v x)) (hl : l≠0)
    (hF : ContDiffAt ℝ 2 F x) (hval : F x=φ (v x))
    (hlo : ∀ᶠ y in 𝓝 x,F y≤φ (v y)) :
    ∃ f : E → ℝ, ContDiffAt ℝ 2 f x ∧ f x=v x ∧
      (∀ᶠ y in 𝓝 x,f y≤v y) ∧
      fderiv ℝ f x=l⁻¹ • fderiv ℝ F x ∧
      ∀ ξ : E, fderiv ℝ (fderiv ℝ f) x ξ ξ=
        l⁻¹*fderiv ℝ (fderiv ℝ F) x ξ ξ-
          (iteratedDeriv 2 φ (v x)/l^3)*(fderiv ℝ F x ξ)^2 := by
  obtain ⟨i,hi,hiv,hiD,hir,hi2⟩ := exists_scalar_inverse_jet hφ hd hl
  let f := i ∘ F
  have hiF : ContDiffAt ℝ 2 i (F x) := hval.symm ▸ hi
  have hiDF : HasDerivAt i l⁻¹ (F x) := hval.symm ▸ hiD
  refine ⟨f,hiF.comp x hF,by dsimp [f]; rw [hval,hiv],?_,?_,?_⟩
  · have hr' := hF.continuousAt.eventually (show ∀ᶠ a in 𝓝 (F x),φ (i a)=a by rwa [hval])
    filter_upwards [hlo,hr'] with y hy hry
    apply hmono.le_iff_le.mp
    simpa only [f,Function.comp_apply,hry] using hy
  · exact (hiDF.comp_hasFDerivAt x (hF.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  · intro ξ
    rw [show f=(fun y => i (F y)) from rfl,second_fderiv_scalar_comp hF hiF ξ,
      hval,hi2,hiD.deriv]
    ring

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma coordinateContact_contDiffAt {a b : M} {q : Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ ∞ (coordinateContact (n := n) a b) q := by
  have hi : ContDiffAt ℝ ∞ (fun z : Model n × (Model n →L[ℝ] ℝ) => ((-1:ℝ),z)) q :=
    contDiffAt_const.prodMk contDiffAt_id
  have hq' := (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) hq).comp q
    hi.contMDiffAt
  have hb' : coordinateBackward a (-1,q.1,q.2)∈(chartAt (Model n) b).source := by
    simpa only [extChartAt_source] using hb
  exact ((contMDiffAt_extChartAt' hb').comp q hq').contDiffAt
end ContactDerivative
end WeakMTWTransport

end

end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondFderivAdd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_add_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun w => f w+g w)) z =
      fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
  have he : fderiv ℝ (fun w => f w+g w) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f w+fderiv ℝ g w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with w hw hw'
    exact fderiv_fun_add (hw.differentiableAt (by norm_num)) (hw'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothTestPDE
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section SmoothTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartTestContact_contDiffAt {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ 1 (chartTestContact a b φ) z := by
  have hA : ContDiffAt ℝ 1 (coordinateContact a b) (z,fderiv ℝ φ z) :=
    (coordinateContact_contDiffAt (a := a) (b := b) (q := (z,fderiv ℝ φ z)) hz hb).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hB : ContDiffAt ℝ 1 (fun w : Model n => (w,fderiv ℝ φ w)) z :=
    contDiffAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num))
  exact hA.comp (f := fun w : Model n => (w,fderiv ℝ φ w)) z hB

end SmoothTestPDE
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartCostCovector_contDiffAt {a b : M} {q : Model n×Model n}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : q.2∈(extChartAt 𝓘(ℝ,Model n) b).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1,(extChartAt 𝓘(ℝ,Model n) b).symm q.2)) :
    ContDiffAt ℝ ∞ (chartCostCovector a b) q := by
  let F : Model n → Model n → ℝ := fun y x =>
    chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y) x
  have hiA := (contMDiffOn_extChartAt_symm (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ha)
  have hiB := (contMDiffOn_extChartAt_symm (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hb)
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) q.swap :=
    (hc.comp q.swap ((hiA.comp q.swap contDiffAt_snd.contMDiffAt).prodMk
      (hiB.comp q.swap contDiffAt_fst.contMDiffAt))).contDiffAt
  exact (ContDiffAt.partial_snd_fderiv hF).comp q (contDiffAt_snd.prodMk contDiffAt_fst)

variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contact_stationarity_eventually {a b : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a q.1 q.2∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1))
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∀ᶠ q' in 𝓝 q, chartCostCovector a b (q'.1,coordinateContact a b q')= -q'.2 := by
  have hY : ContinuousAt (fun q : Model n×(Model n →L[ℝ] ℝ) => coordinateBackward a (-1,q.1,q.2)) q :=
    (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) ha).continuousAt.comp
      (x := q) (continuousAt_const.prodMk continuousAt_id)
  have hT := hY.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb)
  have hA := continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds ha)
  filter_upwards [hT,hA,chartGradientVector_regular_near ha hp] with q' hb' ha' hp'
  dsimp only [chartCostCovector,coordinateContact]
  rw [(extChartAt 𝓘(ℝ,Model n) b).left_inv hb']
  exact (chartCost_gradient_at_contact ha' hp').fderiv

end ContactStationarity
end WeakMTWTransport

end

end

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

lemma second_fderiv_sub {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f a-g a)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ g) x v w := by
  have he : fderiv ℝ (fun a => f a-g a) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f a-fderiv ℝ g a) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with a ha hb
    exact fderiv_fun_sub (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  rw [fderiv_fun_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenteredQuadratic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CenteredQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_half_norm_sq_c2 (z : E) :
    ContDiff ℝ 2 (fun w : E => ‖w-z‖^2/2) :=
  (half_norm_sq_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

lemma centered_half_norm_sq_fderiv (z : E) :
    fderiv ℝ (fun w : E => ‖w-z‖^2/2) z=0 := by
  have hq := (half_norm_sq_hasFDerivAt (z-z)).comp (f := fun w:E => w-z) z ((hasFDerivAt_id z).sub_const z)
  simpa only [Function.comp_def,sub_self,map_zero,ContinuousLinearMap.zero_comp] using hq.fderiv

lemma centered_half_norm_sq_second (z d : E) :
    fderiv ℝ (fderiv ℝ (fun w : E => ‖w-z‖^2/2)) z d d=‖d‖^2 := by
  have hc : ContDiffAt ℝ 2 (fun w:E => ‖w‖^2/2) (z-z) :=
    (half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := second_fderiv_comp_stationary hc (g := fun w:E => w-z)
    (contDiffAt_id.sub contDiffAt_const)
    (by rw [sub_self,half_norm_sq_fderiv,map_zero]) d d
  have hid : fderiv ℝ (fun w:E => w-z) z=ContinuousLinearMap.id ℝ E :=
    ((hasFDerivAt_id z).sub_const z).fderiv
  simpa only [sub_self,hid,ContinuousLinearMap.id_apply,
    half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq] using H
end CenteredQuadratic

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_QuadraticTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section QuadraticTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma diag_bilinear_c2 (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ 2 (fun h : E => B h h/2) := by
  convert! ((B.contDiff.clm_apply contDiff_id).const_smul (1/2:ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  simp only [smul_eq_mul,id_eq]
  ring

lemma diag_bilinear_fderiv (B : E →L[ℝ] E →L[ℝ] ℝ) :
    fderiv ℝ (fun h:E => B h h/2) = fun h => (1/2:ℝ) • (B+B.flip) h := by
  funext h
  have H := (B.hasFDerivAt.clm_apply (hasFDerivAt_id h)).const_smul (1/2:ℝ)
  have hfun : ((1/2:ℝ) • (fun y:E => B y (id y)))=(fun y:E => B y y/2) := by
    ext y
    simp only [Pi.smul_apply,smul_eq_mul,id_eq]
    ring
  rw [hfun] at H
  rw [H.fderiv]
  ext d
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.id_apply,id_eq]

lemma diag_bilinear_second (B : E →L[ℝ] E →L[ℝ] ℝ) (d : E) :
    fderiv ℝ (fderiv ℝ (fun h:E => B h h/2)) 0 d d=B d d := by
  rw [diag_bilinear_fderiv]
  change fderiv ℝ ((1/2:ℝ) • (B+B.flip)) 0 d d=B d d
  rw [ContinuousLinearMap.fderiv]
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

lemma HasLowerSecondTaylor.exists_smooth_minorant {f : E → ℝ}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor f l B) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → ℝ, ContDiffAt ℝ 2 q 0 ∧ q 0=f 0 ∧ fderiv ℝ q 0=l ∧
      (∀ᶠ h in 𝓝 0,q h≤f h) ∧
      ∀ d:E,fderiv ℝ (fderiv ℝ q) 0 d d = B d d-ε*‖d‖^2 := by
  let q : E → ℝ := fun h => f 0+l h+B h h/2-ε*(‖h‖^2/2)
  have hB : ContDiffAt ℝ 2 (fun h:E => B h h/2) 0 := (diag_bilinear_c2 B).contDiffAt
  have hn : ContDiffAt ℝ 2 (fun h:E => ‖h‖^2/2) 0 := by
    simpa only [sub_zero] using (centered_half_norm_sq_c2 (0:E)).contDiffAt
  have hc : ContDiffAt ℝ 2 (fun h:E => f 0+l h) 0 := contDiffAt_const.add l.contDiff.contDiffAt
  refine ⟨q,(hc.add hB).sub (contDiffAt_const.mul hn),by simp [q],?_,?_,?_⟩
  · rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      fderiv_fun_sub ((hc.add hB).differentiableAt (by norm_num))
        ((contDiffAt_const.mul hn).differentiableAt (by norm_num)),
      fderiv_fun_add (hc.differentiableAt (by norm_num)) (hB.differentiableAt (by norm_num)),
      (l.hasFDerivAt.const_add (f 0)).fderiv,diag_bilinear_fderiv]
    have Hn := ((half_norm_sq_hasFDerivAt (0:E)).const_mul ε).fderiv
    rw [Hn]
    simp only [map_zero,smul_zero,add_zero,sub_zero]

  · filter_upwards [hf (ε/2) (by positivity)] with h hh
    dsimp only [q]
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro d
    rw [show q=(fun h => (f 0+l h+B h h/2)-ε*(‖h‖^2/2)) from rfl,
      second_fderiv_sub (hc.add hB) (contDiffAt_const.mul hn),
      second_fderiv_add_eq hc hB,add_apply,add_apply,second_fderiv_const_mul,diag_bilinear_second,
      half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq]
    have hlin : fderiv ℝ (fun h:E => f 0+l h)=fun _ => l := by
      funext h
      exact (l.hasFDerivAt.const_add (f 0)).fderiv
    rw [hlin,(hasFDerivAt_const l (0:E)).fderiv]
    simp only [zero_apply,zero_add]

end QuadraticTest
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_TranslatedMinorant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section TranslatedMinorant
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasLowerSecondTaylor.exists_smooth_minorant_at {f : E → ℝ} {x : E}
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor (fun h => f (x+h)) l B) {ε : ℝ} (hε : 0<ε) :
    ∃ q:E → ℝ,ContDiffAt ℝ 2 q x ∧ q x=f x ∧ fderiv ℝ q x=l ∧
      (∀ᶠ y in 𝓝 x,q y≤f y) ∧
      ∀ d:E,fderiv ℝ (fderiv ℝ q) x d d=B d d-ε*‖d‖^2 := by
  obtain ⟨q,hq,hval,hd,hlo,hH⟩ := hf.exists_smooth_minorant hε
  let Q : E → ℝ := fun y => q (y-x)
  have hQ : ContDiffAt ℝ 2 Q x :=
    (show ContDiffAt ℝ 2 q (x-x) by simpa only [sub_self] using hq).comp (f := fun y:E => y-x) x
      (contDiffAt_id.sub contDiffAt_const)
  have hshift : ∀ y:E,fderiv ℝ Q y=fderiv ℝ q (y-x) := by
    intro y
    simpa only [Q,sub_eq_add_neg] using (fderiv_comp_add_right (-x) (f := q) (x := y))
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · simpa only [Q,sub_self,add_zero] using hval
  · rw [hshift,sub_self,hd]
  · have ht : Tendsto (fun y:E => y-x) (𝓝 x) (𝓝 (0:E)) := by
      convert! ((tendsto_id : Tendsto (fun y:E => y) (𝓝 x) (𝓝 x)).sub
        (tendsto_const_nhds (x := x))) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [sub_self]
    filter_upwards [ht.eventually hlo] with y hy
    simpa only [Q,add_sub_cancel] using hy
  · intro d
    rw [show fderiv ℝ Q=(fun y => fderiv ℝ q (y-x)) from funext hshift]
    have HH := fderiv_comp_add_right (𝕜 := ℝ) (-x) (f := fderiv ℝ q) (x := x)
    simp only [←sub_eq_add_neg,sub_self] at HH
    rw [HH]
    exact hH d

end TranslatedMinorant
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactStationarity
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma chartTestContact_relative_hessian_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    let y := extChartAt 𝓘(ℝ,Model n) b c
    let D := fderiv ℝ (chartCostCovector a b) (z,y)
    fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z =
      -((D.comp (ContinuousLinearMap.inr ℝ (Model n) (Model n))).comp
        (fderiv ℝ (chartTestContact a b φ) z)) := by
  dsimp only
  let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let y := extChartAt 𝓘(ℝ,Model n) b c
  let G := chartCostCovector (n := n) a b
  let T := chartTestContact a b φ
  have hTy : T z=y := rfl
  have hy : y∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source hb
  have hyb : (extChartAt 𝓘(ℝ,Model n) b).symm y=c :=
    (extChartAt 𝓘(ℝ,Model n) b).left_inv hb
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z (fderiv ℝ φ z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,
        (extChartAt 𝓘(ℝ,Model n) b).symm y) := by
    rw [hyb,show c=riemannianExp _ (chartGradientVector a z (fderiv ℝ φ z)) from
      coordinateBackward_eq_exp_chartGradient hz _]
    exact hc
  have hG : DifferentiableAt ℝ G (z,y) :=
    (chartCostCovector_contDiffAt hz hy hc').differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hT : DifferentiableAt ℝ T z :=
    (chartTestContact_contDiffAt hz hφ hb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hgraph : HasFDerivAt (fun w => (w,T w))
      ((ContinuousLinearMap.id ℝ (Model n)).prod (fderiv ℝ T z)) z :=
    (hasFDerivAt_id z).prodMk hT.hasFDerivAt
  have hggraph := hG.hasFDerivAt.comp z hgraph
  have he : (fun w => G (w,T w))=ᶠ[𝓝 z] (fun w => -fderiv ℝ φ w) := by
    have hZ : ContinuousAt (fun w => (w,fderiv ℝ φ w)) z :=
      continuousAt_id.prodMk (hφ.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact hZ.eventually (contact_stationarity_eventually hz hp hb)
  have heD := (hggraph.congr_of_eventuallyEq he.symm).unique
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.neg)
  have hbaseMap : HasFDerivAt (fun w : Model n => (w,y))
      ((ContinuousLinearMap.id ℝ (Model n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hbase := hG.hasFDerivAt.comp (f := fun w : Model n => (w,y)) z hbaseMap
  have hbaseEq : (fun w => G (w,y))=fderiv ℝ (chartCost a c) := by
    funext w
    change fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm y)) w = _
    rw [hyb]
  change HasFDerivAt (fun w => G (w,y)) _ z at hbase
  rw [hbaseEq] at hbase
  have hbaseD := hbase.fderiv
  ext ξ η
  have heV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) heD
  have hbV := congrArg (fun A : Model n →L[ℝ] Model n →L[ℝ] ℝ => A ξ η) hbaseD
  dsimp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,
    neg_apply,Pi.neg_apply] at heV hbV
  have hsplit : (ξ,fderiv ℝ T z ξ)=(ξ,(0:Model n))+(0,fderiv ℝ T z ξ) := by simp
  rw [hsplit,map_add,add_apply] at heV
  change fderiv ℝ (fderiv ℝ φ) z ξ η+fderiv ℝ (fderiv ℝ (chartCost a c)) z ξ η =
    -fderiv ℝ G (z,y) (0,fderiv ℝ T z ξ) η
  simp only [neg_apply,zero_apply] at heV hbV
  linarith only [heV,hbV]

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactConorm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Module

namespace WeakMTWTransport
section NormDetBound
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma norm_eigenvector_image_eq_singularValue (A : E →ₗ[ℝ] F)
    {n : ℕ} (hn : finrank ℝ E=n) (i : Fin n) :
    ‖A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)‖=A.singularValues i := by
  let v := A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i
  have hv : ‖v‖=1 := (A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).norm_eq_one i
  have he : (A.adjoint.comp A) v=A.isSymmetric_adjoint_comp_self.eigenvalues hn i • v :=
    A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  have hsq : ‖A v‖^2=A.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
    rw [←real_inner_self_eq_norm_sq,←A.adjoint_inner_left v (A v)]
    change inner ℝ ((A.adjoint.comp A) v) v=_
    rw [he,real_inner_smul_left,real_inner_self_eq_norm_sq,hv]
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg i)).mp
  rw [hsq,A.sq_singularValues_fin hn i]
end NormDetBound
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_NormDetCoercivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Module

namespace WeakMTWTransport
section NormDetCoercivity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma singularValue_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (i : Fin (finrank ℝ E)) :
    A.singularValues i≤K/b^(finrank ℝ E-1) := by
  classical
  have H : ∀ j : Fin (finrank ℝ E),b≤A.singularValues j := by
    intro j
    have H := hA (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j)
    rw [(A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).norm_eq_one,mul_one,
      norm_eigenvector_image_eq_singularValue] at H
    exact H
  have hp := Finset.prod_le_prod (s := Finset.univ.erase i)
    (fun _ _ => hb.le) (fun index _ => H index)
  have hp' : b^(finrank ℝ E-1)≤∏ j∈Finset.univ.erase i,A.singularValues j := by
    simpa only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin] using hp
  apply (le_div_iff₀ (pow_pos hb _)).mpr
  calc
    A.singularValues i*b^(finrank ℝ E-1) ≤
        A.singularValues i*(∏ j∈Finset.univ.erase i,A.singularValues j) :=
      mul_le_mul_of_nonneg_left hp' (A.singularValues_nonneg i)
    _ = A.normDet := by
      rw [A.normDet_eq_prod_singularValues,←Fin.prod_univ_eq_prod_range]
      exact Finset.mul_prod_erase Finset.univ (fun j : Fin (finrank ℝ E) => A.singularValues j) (Finset.mem_univ i)
    _ ≤ K := hK

lemma norm_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (v : E) :
    ‖A v‖≤((finrank ℝ E:ℝ)*K/b^(finrank ℝ E-1))*‖v‖ := by
  classical
  let e := A.isSymmetric_adjoint_comp_self.eigenvectorBasis (rfl : finrank ℝ E=finrank ℝ E)
  have hσ := singularValue_le_of_conorm_det A hb hA hK
  have hK0 : 0≤K := A.normDet_nonneg.trans hK
  have hC : 0≤K/b^(finrank ℝ E-1) := div_nonneg hK0 (pow_pos hb _).le
  calc
    ‖A v‖ = ‖∑ j : Fin (finrank ℝ E), e.repr v j • A (e j)‖ := by
      simp_rw [←map_smul]
      rw [←map_sum,e.sum_repr]
    _ ≤ ∑ j : Fin (finrank ℝ E),‖e.repr v j • A (e j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin (finrank ℝ E),(K/b^(finrank ℝ E-1))*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,norm_eigenvector_image_eq_singularValue]
      have he : ‖e.repr v j‖≤‖v‖ := by
        rw [e.repr_apply_apply]
        simpa only [e.norm_eq_one,mul_one,one_mul] using (norm_inner_le_norm (e j) v)
      calc
        ‖e.repr v j‖*A.singularValues j ≤ ‖v‖*(K/b^(finrank ℝ E-1)) :=
          mul_le_mul he (hσ j) (A.singularValues_nonneg j) (norm_nonneg v)
        _ = _ := mul_comm _ _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end NormDetCoercivity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CoerciveBilinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearOperator_conorm {W : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hW : ∀ d:E,m*‖d‖^2≤W d d) (d : E) : m*‖d‖≤‖bilinearOperator W d‖ := by
  by_cases hd : d=0
  · simp [hd]
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hd)).mp
  calc
    (m*‖d‖)*‖d‖=m*‖d‖^2 := by ring
    _ ≤ W d d := hW d
    _ = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _

lemma bilinear_quadratic_bound_of_det {W : E →L[ℝ] E →L[ℝ] ℝ} {m K : ℝ}
    (hm : 0 < m) (hW : ∀ d:E,m*‖d‖^2≤W d d)
    (hK : |(bilinearOperator W).det|≤K) (d : E) :
    W d d≤((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖^2 := by
  have hK' : (bilinearOperator W).toLinearMap.normDet≤K := by
    rwa [LinearMap.normDet_eq_abs_det]
  have H := norm_le_of_conorm_det (bilinearOperator W).toLinearMap hm
    (bilinearOperator_conorm hW) hK' d
  calc
    W d d = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _
    _ ≤ (((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖)*‖d‖ :=
      mul_le_mul_of_nonneg_right H (norm_nonneg d)
    _ = _ := by ring
end CoerciveBilinear

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RelativeHessianBound
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalUniformRelativeHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma relative_hessian_operator_factor_fixed {a b : M} {z : Model n} {φ : Model n → ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (hφ : ContDiffAt ℝ 2 φ z)
    (hp : chartGradientVector a z (fderiv ℝ φ z)∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z))
    (hb : coordinateBackward a (-1,z,fderiv ℝ φ z)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
    bilinearOperator (fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z) =
      (mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b c)).comp
        (fderiv ℝ (chartTestContact a b φ) z) := by
  dsimp only
  rw [chartTestContact_relative_hessian_fixed hz hφ hp hb]
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  simp only [ContinuousLinearMap.comp_apply,bilinearOperator_inner,mixedCostOperator,
    neg_apply]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mixedCostOperator_continuousAt {a b : M} {q : Model n×Model n}
    (ha : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : q.2∈(extChartAt 𝓘(ℝ,Model n) b).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1,(extChartAt 𝓘(ℝ,Model n) b).symm q.2)) :
    ContinuousAt (fun q : Model n×Model n => mixedCostOperator a b q.1 q.2) q := by
  have H := ((chartCostCovector_contDiffAt ha hb hc).fderiv_right
    (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  exact continuousAt_const.clm_comp ((H.clm_comp continuousAt_const).neg)

variable [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_strict_relative_hessian_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0<lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let za := extChartAt 𝓘(ℝ,Model n) a a
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)), N∈𝓝 (za,L) ∧
    ∃ C≥0,∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (φ : Model n → ℝ), (z,fderiv ℝ φ z)∈N →
      ContDiffAt ℝ 2 φ z →
      uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z →
      (∃ ε>0,∀ᶠ w in 𝓝 z,ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d≤C*‖d‖^2 := by
  dsimp only
  let za := extChartAt 𝓘(ℝ,Model n) a a
  let b := coordinateBackward a (-1,za,L)
  let yb := extChartAt 𝓘(ℝ,Model n) b b
  let Y := fun q : Model n×(Model n →L[ℝ] ℝ) => coordinateBackward a (-1,q.1,q.2)
  let J := fun q : Model n×(Model n →L[ℝ] ℝ) => (q.1,extChartAt 𝓘(ℝ,Model n) b (Y q))
  have ha : za∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hb : yb∈(extChartAt 𝓘(ℝ,Model n) b).target :=
    (extChartAt 𝓘(ℝ,Model n) b).map_source (mem_extChartAt_source b)
  have hY : ContinuousAt Y (za,L) :=
    (coordinateBackward_contMDiffAt (q := (-1,za,L)) ha).continuousAt.comp
      (x := (za,L)) (continuousAt_const.prodMk continuousAt_id)
  have hJ : ContinuousAt J (za,L) := continuousAt_fst.prodMk
    ((show ContinuousAt (extChartAt 𝓘(ℝ,Model n) b) (Y (za,L)) from continuousAt_extChartAt b).comp (x := (za,L)) (f := Y) hY)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm za,chartGradientVector a za L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z:M×M => cost z.1 z.2)
      ((extChartAt 𝓘(ℝ,Model n) a).symm za,(extChartAt 𝓘(ℝ,Model n) b).symm yb) := by
    rw [(extChartAt 𝓘(ℝ,Model n) b).left_inv (mem_extChartAt_source b)]
    rw [show b=riemannianExp _ (chartGradientVector a za L) from coordinateBackward_eq_exp_chartGradient ha _]
    exact hc
  let F := fun q : Model n×(Model n →L[ℝ] ℝ) =>
    |(mixedCostOperator a b (J q).1 (J q).2).det|
  have hF : ContinuousAt F (za,L) :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((mixedCostOperator_continuousAt ha hb hc').comp hJ)).abs
  let B := F (za,L)+1
  have hB : 0≤B := by dsimp [B,F] <;> positivity
  have hFn : ∀ᶠ q in 𝓝 (za,L),F q≤B :=
    (hF.eventually (gt_mem_nhds (show F (za,L)<B by dsimp [B] <;> linarith))).mono (fun _ h => h.le)
  obtain ⟨U,hU,haU,V,hV,hbV,K,hK,HK⟩ := hmtw.exists_locally_uniform_test_det_bound hlam hcap a b
  let N := {q : Model n×(Model n →L[ℝ] ℝ) | q.1∈U ∧
    q.1∈(extChartAt 𝓘(ℝ,Model n) a).target ∧ Y q∈V ∧
    Y q∈(extChartAt 𝓘(ℝ,Model n) b).source ∧
    chartGradientVector a q.1 q.2∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) ∧ F q≤B}
  have hN : N∈𝓝 (za,L) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hU.mem_nhds haU),
      continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds ha),
      hY.preimage_mem_nhds (hV.mem_nhds hbV),
      hY.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) b),
      chartGradientVector_regular_near ha hp,hFn] with q h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  let C := (finrank ℝ (Model n):ℝ)*(B*K)/m^(finrank ℝ (Model n)-1)
  refine ⟨N,hN,C,by dsimp [C] <;> positivity,?_⟩
  intro x0 uv huv z φ hz hφ hval hgap hpos d
  obtain ⟨hzU,hzT,hYV,hYS,hpφ,hBφ⟩ := hz
  have hdet := HK z hzU x0 uv huv φ hφ hYV hpφ hval hgap ⟨m,hm,hpos⟩
  let c := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let W := fderiv ℝ (fderiv ℝ φ) z+fderiv ℝ (fderiv ℝ (chartCost a c)) z
  have hfactor := relative_hessian_operator_factor_fixed hzT hφ hpφ hYS
  have hWdet : |(bilinearOperator W).det|≤B*K := by
    rw [hfactor]
    change |((mixedCostOperator a b z (extChartAt 𝓘(ℝ,Model n) b c)).toLinearMap.comp
      (fderiv ℝ (chartTestContact a b φ) z).toLinearMap).det|≤_
    rw [LinearMap.det_comp,abs_mul]
    exact mul_le_mul hBφ hdet (abs_nonneg _) hB
  exact bilinear_quadratic_bound_of_det hm hpos hWdet d

end LocalUniformRelativeHessian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ActualRelativeHessianBound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActualRelativeHessianBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_relative_hessian_bound
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0<lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m : ℝ} (hm : 0 < m) :
    let za := extChartAt 𝓘(ℝ,Model n) a a
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)), N∈𝓝 (za,L) ∧
    ∃ C≥0,∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (φ : Model n → ℝ), (z,fderiv ℝ φ z)∈N →
      ContDiffAt ℝ 2 φ z →
      uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z →
      (∀ᶠ w in 𝓝 z,φ w≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)) →
      (∀ d : Model n,m*‖d‖^2≤fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d) →
      ∀ d : Model n,fderiv ℝ (fderiv ℝ φ) z d d+
        fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,fderiv ℝ φ z)))) z d d≤C*‖d‖^2 := by
  dsimp only
  obtain ⟨N,hN,C,hC,H⟩ := hmtw.exists_local_strict_relative_hessian_bound hlam hcap a L hp
    (show 0 < m/2 by positivity)
  refine ⟨N,hN,C+m/2,by positivity,?_⟩
  intro x0 uv huv z φ hz hφ hval hlo hpos d
  let b := coordinateBackward a (-1,z,fderiv ℝ φ z)
  let q : Model n → ℝ := fun w => ‖w-z‖^2/2
  let ψ : Model n → ℝ := fun w => φ w-(m/2)*q w
  have hq : ContDiffAt ℝ 2 q z := (centered_half_norm_sq_c2 z).contDiffAt
  have hψ : ContDiffAt ℝ 2 ψ z := hφ.sub (contDiffAt_const.mul hq)
  have hψL : fderiv ℝ ψ z=fderiv ℝ φ z := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      fderiv_fun_sub (hφ.differentiableAt (by norm_num))
        ((hq.differentiableAt (by norm_num)).const_mul _)]
    change fderiv ℝ φ z-fderiv ℝ ((m/2) • q) z=fderiv ℝ φ z
    rw [fderiv_const_smul_field,Pi.smul_apply,centered_half_norm_sq_fderiv,smul_zero,sub_zero]
  have hψval : uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)=ψ z := by simpa [ψ,q] using hval
  have hgap : ∃ ε>0,∀ᶠ w in 𝓝 z,
      ε*dist w z^2≤uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)-ψ w := by
    refine ⟨m/4,by positivity,?_⟩
    filter_upwards [hlo] with w hw
    dsimp only [ψ,q]
    rw [dist_eq_norm]
    nlinarith only [hw]
  have hψH (e : Model n) : fderiv ℝ (fderiv ℝ ψ) z e e=
      fderiv ℝ (fderiv ℝ φ) z e e-(m/2)*‖e‖^2 := by
    rw [show ψ=(fun w => φ w-(m/2)*q w) from rfl,
      second_fderiv_sub hφ (contDiffAt_const.mul hq),second_fderiv_const_mul,
      centered_half_norm_sq_second]
  have hpψ : ∀ e : Model n,(m/2)*‖e‖^2≤fderiv ℝ (fderiv ℝ ψ) z e e+
      fderiv ℝ (fderiv ℝ (chartCost a b)) z e e := by
    intro e
    rw [hψH]
    linarith only [hpos e]
  have HD := H x0 uv huv z ψ (by rw [hψL]; exact hz) hψ hψval hgap
    (by simpa only [hψL] using hpψ) d
  rw [hψH,hψL] at HD
  nlinarith only [HD]

end ActualRelativeHessianBound
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalOuterJetBound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalOuterJetBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_outer_chart_jet_bound_oai
    (hmtw : WeakMTW (n := n) (M := M)) {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (a : M) (L : Model n →L[ℝ] ℝ)
    (hp : chartGradientVector a (extChartAt 𝓘(ℝ,Model n) a a) L∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a a)))
    {m lmax : ℝ} (hm : 0 < m) (hlmax : 0 < lmax) :
    ∃ N : Set (Model n×(Model n →L[ℝ] ℝ)),
      N∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a,L) ∧ ∃ C≥0,
      ∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ (z : Model n) (c : Model n → ℝ) (l:ℝ),0 < l → l≤lmax →
      ContDiffAt ℝ 2 c z → (z,l⁻¹ • (-fderiv ℝ c z))∈N →
      (∀ d:Model n,2*m*l*‖d‖^2≤
        l*fderiv ℝ (fderiv ℝ (chartCost a
          (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z d d-
          fderiv ℝ (fderiv ℝ c) z d d) →
      ∀ φ:ℝ → ℝ,StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      HasDerivAt φ l (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z)) →
      iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm z))≤0 →
      ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
      HasLowerSecondTaylor (fun h => φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (z+h)))+
        c (z+h)) 0 H → ∀ d,H d d≤C*‖d‖^2 := by
  obtain ⟨N,hN,C,hC,HC⟩ := hmtw.exists_local_relative_hessian_bound hlam hcap a L hp hm
  refine ⟨N,hN,lmax*(C+m),mul_nonneg hlmax.le (add_nonneg hC hm.le),?_⟩
  intro x0 uv huv z c l hl hll hc hNq hbase φ hmono hφ hd hconc H hH hjet d
  let v : Model n → ℝ := fun w => uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm w)
  let A := fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,l⁻¹ • (-fderiv ℝ c z))))) z
  obtain ⟨q,hq,hq0,hqD,hqlo,hqH⟩ := hjet.exists_smooth_minorant_at (f := fun w => φ (v w)+c w) (x := z) (l := 0) (B := H) (mul_pos hm hl)
  let F : Model n → ℝ := fun w => q w-c w
  have hF : ContDiffAt ℝ 2 F z := hq.sub hc
  have hF0 : F z=φ (v z) := by
    dsimp only [F,v]
    rw [hq0]
    ring
  have hFlo : ∀ᶠ w in 𝓝 z,F w≤φ (v w) := by
    filter_upwards [hqlo] with w hw
    change q w≤φ (v w)+c w at hw
    dsimp only [F]
    linarith only [hw]
  have hFD : fderiv ℝ F z= -fderiv ℝ c z := by
    rw [show F=(fun w => q w-c w) from rfl,
      fderiv_fun_sub (hq.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
      hqD,zero_sub]
  obtain ⟨f,hf,hf0,hflo,hfD,hfH⟩ := scalar_inverse_lower_test (E := Model n) (v := v) (F := F) (x := z) hmono hφ hd hl.ne' hF hF0 hFlo
  have hfD' : fderiv ℝ f z=l⁻¹ • (-fderiv ℝ c z) := by rw [hfD,hFD]
  have Heq (e:Model n) : l*(fderiv ℝ (fderiv ℝ f) z e e+A e e)=
      H e e-(m*l)*‖e‖^2+(l*A e e-fderiv ℝ (fderiv ℝ c) z e e)-
        (iteratedDeriv 2 φ (v z)/l^2)*(fderiv ℝ F z e)^2 := by
    rw [hfH,show F=(fun w => q w-c w) from rfl,second_fderiv_sub hq hc,hqH]
    field_simp [hl.ne']
    ring
  have hscalar (e:Model n) :
      0≤ -(iteratedDeriv 2 φ (v z)/l^2)*(fderiv ℝ F z e)^2 :=
    mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (sq_nonneg l))) (sq_nonneg _)
  have hpos (e:Model n) : m*‖e‖^2≤fderiv ℝ (fderiv ℝ f) z e e+A e e := by
    apply (mul_le_mul_iff_right₀ hl).mp
    rw [Heq]
    have hb := hbase e
    change 2*m*l*‖e‖^2≤l*A e e-fderiv ℝ (fderiv ℝ c) z e e at hb
    nlinarith only [hb,hH e,hscalar e]
  have HB := HC x0 uv huv z f (by rwa [hfD']) hf hf0.symm hflo
    (by simpa only [hfD'] using hpos) d
  rw [hfD'] at HB
  change fderiv ℝ (fderiv ℝ f) z d d+A d d≤C*‖d‖^2 at HB
  have HB' := mul_le_mul_of_nonneg_left HB hl.le
  rw [Heq] at HB'
  have Hb := hbase d
  change 2*m*l*‖d‖^2≤l*A d d-fderiv ℝ (fderiv ℝ c) z d d at Hb
  have Hzero : 0≤2*m*l*‖d‖^2 := by positivity
  have HC' : l*(C+m)*‖d‖^2≤lmax*(C+m)*‖d‖^2 := by
    gcongr
  nlinarith only [HB',Hb,Hzero,hscalar d,HC']

end LocalOuterJetBound
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound_oai.{u_1}
