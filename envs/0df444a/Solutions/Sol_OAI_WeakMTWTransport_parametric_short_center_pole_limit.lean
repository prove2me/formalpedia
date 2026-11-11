-- Prove2me | solution 1 for OAI.WeakMTWTransport.parametric_short_center_pole_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:04.345775+00:00
-- url     : https://prove2.me/submissions/db9f21a3-32ff-49f6-90dd-a87ec2413743

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_parametric_short_lower_sequence

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
lemma shortForward_zero {a : M} {ψ : Model n → ℝ} {y : Model n}
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).target) : shortForward a ψ (0,y)=y := by
  simp only [shortForward,zero_smul,coordinateBackward,map_zero,smul_zero]
  rw [movingNormal_zero hy,(extChartAt 𝓘(ℝ,Model n) a).right_inv hy]

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ShortGradientLimit
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

lemma parametric_short_gradient_tendsto {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i))
    (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (parametricShortForward a ψ ((pj i,tj i),xj i))) :
    Tendsto (fun i=>fderiv ℝ
      (fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (parametricShortForward a ψ ((pj i,tj i),xj i))) atTop
      (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) := by
  obtain ⟨U,hU,hD,_⟩ := exists_parametric_short_lower_sequence L hx hψ hp hxx ht htpos hlip hbelow htouch
  apply hD.congr'
  filter_upwards [hU,hd] with i hi hdi
  let z := parametricShortForward a ψ ((pj i,tj i),xj i)
  let F := fun w=>hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)
  have hm : IsLocalMin (fun w=>F w-U i w) z := by
    filter_upwards [hi.2.2] with w hw
    change F z-U i z≤F w-U i w
    rw [hi.2.1]
    linarith only [hw]
  have he := hm.fderiv_eq_zero
  rw [fderiv_fun_sub hdi (hi.1.differentiableAt (by norm_num))] at he
  exact (sub_eq_zero.mp he).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterPoleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterPoleLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] in
lemma coordinateBackward_negative_support_center {c : M} {v s l : ℝ}
    {r : Model n} {φ : ℝ → ℝ} (hs : s≠0)
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (hφ : HasDerivAt φ l v) :
    coordinateBackward c (1, extChartAt 𝓘(ℝ,Model n) c c,
      -fderiv ℝ (fun w=>coordinateScalarSupport c φ
        (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
          (extChartAt 𝓘(ℝ,Model n) c c))=riemannianExp c (l • r) := by
  let x := extChartAt 𝓘(ℝ,Model n) c c
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target :=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  have hL (d:Model n) : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).symmL ℝ c d=d := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) c)]
    exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source c)
  have hr' : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) c).symm x) r∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm x) := by
    dsimp only [x]
    rw [hb]
    simpa only [hL] using hr
  rw [(coordinateScalarSupport_hasFDerivAt hx hs hr' hφ).fderiv]
  simp only [coordinateBackward,map_neg,map_smul,neg_smul,one_smul,neg_neg]
  rw [movingNormal_eq hx,hb,hL]
  change riemannianExp c (l • (riemannianCoordinateMetric c x).inverse ((riemannianCoordinateMetric c x) r))=_
  rw [(riemannianCoordinateMetric_isInvertible hx).inverse_apply_self]

lemma parametric_short_center_pole_limit_oai {a c : M} {ψ : P×Model n → ℝ}
    {p : P} (L : ℝ≥0)
    (hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c))
    {r : Model n} {v s l : ℝ} {φ : ℝ → ℝ} (hs : s≠0)
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (hφ : HasDerivAt φ l v)
    (heq : (fun w=>ψ (p,w))=fun w=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),w))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj τj : ℕ → ℝ}
    {f : ℕ → M → ℝ} {F : ℕ → Model n → ℝ} {aj : ℕ → M}
    (hp : Tendsto pj atTop (𝓝 p))
    (hxx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (ht : Tendsto tj atTop (𝓝 1)) (hτ : Tendsto τj atTop (𝓝 0))
    (ha : Tendsto aj atTop (𝓝 a)) (hτpos : ∀ᶠ i in atTop,0<τj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) c).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i))=ψ (pj i,xj i))
    (hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)))
    (herr : Tendsto (fun i=>fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i))+
      fderiv ℝ (fun w=>hopfLax (τj i) (f i) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i))) atTop (𝓝 0))
    (hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=aj i) :
    a=riemannianExp c (l • r) := by
  let x := extChartAt 𝓘(ℝ,Model n) c c
  let z := fun i=>parametricShortForward c ψ ((pj i,τj i),xj i)
  let j := fderiv ℝ (fun w=>ψ (p,w)) x
  have hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target :=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hG := parametric_short_gradient_tendsto L hx hψ hp hxx hτ hτpos hlip hbelow htouch hd
  have hF : Tendsto (fun i=>fderiv ℝ (F i) (z i)) atTop (𝓝 (-j)) := by
    convert herr.sub hG using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [add_sub_cancel_right,zero_sub,j,z,x])
  have hz : Tendsto z atTop (𝓝 x) := by
    have HH := (parametricShortForward_contDiffAt hx hψ).continuousAt.tendsto.comp
      ((hp.prodMk_nhds hτ).prodMk_nhds hxx)
    change Tendsto z atTop (𝓝 (parametricShortForward c ψ ((p,0),x))) at HH
    convert HH using 1
    all_goals try with_reducible_and_instances rfl
    simp only [parametricShortForward,shortForward_zero hx]
  have HB := (coordinateBackward_contMDiffAt (q := (1,x,-j)) hx).continuousAt.tendsto.comp
    (ht.prodMk_nhds (hz.prodMk_nhds hF))
  have HE : coordinateBackward c (1,x,-j)=a := tendsto_nhds_unique (HB.congr' hback) ha
  rw [←HE]
  dsimp only [j,x]
  rw [heq]
  exact coordinateBackward_negative_support_center hs hr hφ

end CenterPoleLimit
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWTransport.parametric_short_center_pole_limit_oai.{u_1, u_2} := @OAI.WeakMTWTransport.parametric_short_center_pole_limit_oai.{u_1, u_2}
