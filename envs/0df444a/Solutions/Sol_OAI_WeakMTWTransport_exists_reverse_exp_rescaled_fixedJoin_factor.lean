-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_reverse_exp_rescaled_fixedJoin_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:51.513376+00:00
-- url     : https://prove2.me/submissions/7cabb7f3-48c8-4043-bb0d-0cd047d3d702

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
import Definitions.Def_OAIQ232A026

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
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

lemma second_fderiv_comp_affine {f : F → ℝ} (L : E →L[ℝ] F) (b : F) (x : E)
    (hf : ContDiffAt ℝ 2 f (b+L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (b+L h))) x v w =
      fderiv ℝ (fderiv ℝ f) (b+L x) (L v) (L w) := by
  have hL : ∀ y:E, HasFDerivAt (fun h : E => b+L h) L y :=
    fun y => (L.hasFDerivAt (x := y)).const_add b
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun h : E => b+L h) x (hL x)
  have H := hd.clm_comp (hasFDerivAt_const L x)
  have heq : (fun h => fderiv ℝ f (b+L h) |>.comp L) =ᶠ[𝓝 x]
      (fderiv ℝ (fun h => f (b+L h))) := by
    have hn := (hL x).continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hn] with h hh
    exact ((hh.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun h : E => b+L h) h (hL h)).fderiv.symm
  have he := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w)
    (H.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,map_zero,ContinuousLinearMap.comp_zero,
    zero_add,add_apply,zero_apply] using he

end

open Set Filter
open scoped Topology ContDiff

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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SliceDerivatives
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

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fderiv_snd_slice {f : F×E → G} {a : F} {b : E}
    (hf : DifferentiableAt ℝ f (a,b)) (k : E) :
    fderiv ℝ (fun v : E => f (a,v)) b k=fderiv ℝ f (a,b) (0,k) := by
  have H := hf.hasFDerivAt.comp (f := fun v : E => (a,v)) b
    ((hasFDerivAt_const a b).prodMk (hasFDerivAt_id (𝕜 := ℝ) b))
  have HH := congrArg (fun L : E →L[ℝ] G => L k) H.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using HH

lemma second_fderiv_snd_slice {f : F×E → ℝ} {a : F} {b : E}
    (hf : ContDiffAt ℝ 2 f (a,b)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun t : E => f (a,t))) b v w=
      fderiv ℝ (fderiv ℝ f) (a,b) (0,v) (0,w) := by
  let I : E →L[ℝ] F×E := (0:E →L[ℝ] F).prod (ContinuousLinearMap.id ℝ E)
  have H := second_fderiv_comp_affine I (a,0) b (by simpa [I] using hf) v w
  simpa [I] using H

lemma second_fderiv_map_fst {B : F×G → ℝ} {e : E → F} {x : E} {y : G}
    (hB : ContDiffAt ℝ 2 B (e x,y)) (he : ContDiffAt ℝ 2 e x) (d : E) (k : G) :
    fderiv ℝ (fderiv ℝ (fun q : E×G => B (e q.1,q.2))) (x,y) (d,0) (0,k)=
      fderiv ℝ (fderiv ℝ B) (e x,y) (fderiv ℝ e x d,0) (0,k) := by
  let A := fun q : E×G => B (e q.1,q.2)
  have hA : ContDiffAt ℝ 2 A (x,y) :=
    hB.comp (x,y) ((he.comp (x,y) contDiffAt_fst).prodMk contDiffAt_snd)
  have hdA := (((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a : E => (a,y)) x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))).clm_apply
        (hasFDerivAt_const ((0:E),k) x)
  have hdB := (((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a : E => (e a,y)) x
      ((he.differentiableAt (by norm_num)).hasFDerivAt.prodMk (hasFDerivAt_const y x))).clm_apply
        (hasFDerivAt_const ((0:F),k) x)
  have hnA : ∀ᶠ a in 𝓝 x, ContDiffAt ℝ 2 A (a,y) :=
    (continuousAt_id.prodMk continuousAt_const).eventually (hA.eventually (by norm_num))
  have hnB : ∀ᶠ a in 𝓝 x, ContDiffAt ℝ 2 B (e a,y) :=
    (he.continuousAt.prodMk continuousAt_const).eventually (hB.eventually (by norm_num))
  have heq : (fun a : E => fderiv ℝ A (a,y) (0,k)) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ B (e a,y) (0,k)) := by
    filter_upwards [hnA,hnB] with a ha hb
    rw [←fderiv_snd_slice (ha.differentiableAt (by norm_num)) k,
      ←fderiv_snd_slice (hb.differentiableAt (by norm_num)) k]
  have H := congrArg (fun L : E →L[ℝ] ℝ => L d)
    ((hdA.congr_of_eventuallyEq heq.symm).unique hdB)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,map_zero,zero_apply,
    add_apply,add_zero,zero_add] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalInverseCalculus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma local_inverse_derivative {e : F → E} {L : E → F} {p : E}
    (he : DifferentiableAt ℝ e (L p)) (hL : DifferentiableAt ℝ L p)
    (hid : (fun v => e (L v)) =ᶠ[𝓝 p] (fun v => v)) (v : E) :
    fderiv ℝ e (L p) (fderiv ℝ L p v)=v := by
  have H := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp p he hL,fderiv_fun_id] at H
  exact congrArg (fun A : E →L[ℝ] E => A v) H


end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LogActionMixed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma logJoinAction_contDiffAt {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : ContDiffAt ℝ ∞ P p)
    (hg : ContDiffAt ℝ ∞ g p) (hg0 : g p=0) :
    ContDiffAt ℝ ∞ (logJoinAction z a P g) (q,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hA : ContMDiffAt 𝓘(ℝ,V×E) 𝓘(ℝ,Model n) ∞
      (fun w : V×E => riemannianExp z (g w.2)) (q,p) :=
    (contMDiff_riemannianExp_fiber z _).comp (q,p)
      ((hg.comp (q,p) contDiffAt_snd).contMDiffAt)
  have hB : ContMDiffAt 𝓘(ℝ,V×E) 𝓘(ℝ,Model n) ∞
      (fun w : V×E => riemannianExp z w.1) (q,p) :=
    (contMDiff_riemannianExp_fiber z _).comp (q,p) contDiffAt_fst.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun w : M×M => cost w.1 w.2) (riemannianExp z (g p),riemannianExp z q) := by
    simpa only [hg0,riemannianExp_zero] using
      cost_contMDiffAt_of_injectivityDomain
        (⟨z,q⟩ : TangentBundle 𝓘(ℝ,Model n) M) hq
  have HC := (hC.comp (f := fun w : V×E =>
    (riemannianExp z (g w.2),riemannianExp z w.1)) (q,p) (hA.prodMk hB)).contDiffAt
  change ContDiffAt ℝ ∞ (fun w : V×E => normalCost z w.1 (g w.2)) (q,p) at HC
  exact (hP.comp (q,p) contDiffAt_snd).add (contDiffAt_const.mul HC)

lemma logJoinAction_middle_gradient {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : DifferentiableAt ℝ P p)
    (hg : DifferentiableAt ℝ g p) (hg0 : g p=0)
    (hB : DifferentiableAt ℝ (logJoinAction z a P g) (q,p)) (k : E) :
    fderiv ℝ (logJoinAction z a P g) (q,p) (0,k)=
      fderiv ℝ P p k-a*inner ℝ q (fderiv ℝ g p k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hC : DifferentiableAt ℝ (normalCost z q) (g p) := by
    rw [hg0]
    exact (normalCost_contDiffAt hq).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := hP.hasFDerivAt.add ((hC.hasFDerivAt.comp p hg.hasFDerivAt).const_smul a)
  have HI := (hasFDerivAt_const q p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD := hB.hasFDerivAt.comp (f := fun b : E => (q,b)) p HI
  have H := congrArg (fun L : E →L[ℝ] ℝ => L k) (hD.unique hd)
  change fderiv ℝ (logJoinAction z a P g) (q,p) (0,k)=
    fderiv ℝ P p k+a*fderiv ℝ (normalCost z q) (g p) (fderiv ℝ g p k) at H
  rw [hg0,normalCost_fderiv_zero hq] at H
  linarith

lemma logJoinAction_mixed {z : M} {a : ℝ} {P : E → ℝ}
    {g : E → TangentSpace 𝓘(ℝ,Model n) z} {p : E}
    {q : TangentSpace 𝓘(ℝ,Model n) z}
    (hq : q∈injectivityDomain z) (hP : ContDiffAt ℝ ∞ P p)
    (hg : ContDiffAt ℝ ∞ g p) (hg0 : g p=0)
    (d : TangentSpace 𝓘(ℝ,Model n) z) (k : E) :
    fderiv ℝ (fderiv ℝ (logJoinAction z a P g)) (q,p) (d,0) (0,k)=
      -a*inner ℝ d (fderiv ℝ g p k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z
  have hB := logJoinAction_contDiffAt hq hP hg hg0 (a := a)
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HI := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const p q)
  have hd := (((hB2.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun r : V => (r,p)) q HI).clm_apply
      (hasFDerivAt_const ((0:V),k) q)
  have he : (fun r : V => fderiv ℝ (logJoinAction z a P g) (r,p) (0,k)) =ᶠ[𝓝 q]
      (fun r => fderiv ℝ P p k-a*inner ℝ r (fderiv ℝ g p k)) := by
    filter_upwards [(isOpen_injectivityDomain z).mem_nhds hq] with r hr
    exact logJoinAction_middle_gradient hr (hP.differentiableAt (by simp))
      (hg.differentiableAt (by simp)) hg0
      ((logJoinAction_contDiffAt hr hP hg hg0).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) k
  have hi : HasFDerivAt (fun r : V => fderiv ℝ P p k-a*inner ℝ r (fderiv ℝ g p k))
      (-a • innerSL ℝ (fderiv ℝ g p k)) q := by
    convert! ((((innerSL ℝ (fderiv ℝ g p k)).hasFDerivAt (x := q)).const_smul (-a)).const_add
      (fderiv ℝ P p k)) using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg,real_inner_comm,neg_mul,innerSL_apply_apply]
  have H := congrArg (fun L : V →L[ℝ] ℝ => L d)
    ((hd.congr_of_eventuallyEq he.symm).unique hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,zero_add,
    ContinuousLinearMap.comp_zero,ContinuousLinearMap.flip_apply,
    smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_comm] at H
  exact H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalLogMixed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma normalCost_log_contDiffAt {x : M} {e : F → TangentSpace 𝓘(ℝ,Model n) x}
    {b : F} (he : ContDiffAt ℝ ∞ e b) (hp : e b∈injectivityDomain x) :
    ContDiffAt ℝ ∞ (fun q : F×TangentSpace 𝓘(ℝ,Model n) x => normalCost x (e q.1) q.2) (b,0) := by
  have H := logJoinAction_contDiffAt hp (contDiffAt_const (c := (0:ℝ)))
    (contDiffAt_id (𝕜 := ℝ)) rfl (a := 1)
  have HH := H.comp (b,0) ((he.comp (b,0) contDiffAt_fst).prodMk contDiffAt_snd)
  simpa only [logJoinAction,zero_add,one_mul,Function.comp_def,id_eq] using HH

lemma normalCost_log_mixed {x : M} {e : F → TangentSpace 𝓘(ℝ,Model n) x}
    {b : F} (he : ContDiffAt ℝ ∞ e b) (hp : e b∈injectivityDomain x)
    (d : F) (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (fun q : F×TangentSpace 𝓘(ℝ,Model n) x =>
      normalCost x (e q.1) q.2)) (b,0) (d,0) (0,k) = -inner ℝ (fderiv ℝ e b d) k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := logJoinAction x (1:ℝ) (fun _:V => (0:ℝ)) (id:V→V)
  have hB : ContDiffAt ℝ ∞ B (e b,0) :=
    logJoinAction_contDiffAt hp contDiffAt_const contDiffAt_id rfl
  have heq : (fun q : F×V => normalCost x (e q.1) q.2)=(fun q => B (e q.1,q.2)) := by
    ext q; simp only [B,logJoinAction,zero_add,one_mul,id_eq]
  rw [heq,second_fderiv_map_fst
    (hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (he.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have H := logJoinAction_mixed hp (contDiffAt_const (c := (0:ℝ)))
    (contDiffAt_id (𝕜 := ℝ)) rfl (a := 1) (fderiv ℝ e b d) k
  simpa only [B,fderiv_id,ContinuousLinearMap.id_apply,neg_one_mul] using H

lemma normal_log_derivatives_adjoint {x y : M}
    {e : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x}
    {f : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (he : ContDiffAt ℝ ∞ e 0) (hf : ContDiffAt ℝ ∞ f 0)
    (hep : e 0∈injectivityDomain x) (hfq : f 0∈injectivityDomain y)
    (hei : ∀ᶠ v in 𝓝 0, riemannianExp x (e v)=riemannianExp y v)
    (hfi : ∀ᶠ u in 𝓝 0, riemannianExp y (f u)=riemannianExp x u)
    (d : TangentSpace 𝓘(ℝ,Model n) y) (k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (fderiv ℝ e 0 d) k=inner ℝ d (fderiv ℝ f 0 k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  let A : W×V → ℝ := fun q => normalCost x (e q.1) q.2
  let B : V×W → ℝ := fun q => normalCost y (f q.1) q.2
  have hA := normalCost_log_contDiffAt he hep
  have hB := normalCost_log_contDiffAt hf hfq
  have hA2 := hA.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq : A =ᶠ[𝓝 (0,0)] (fun q => B q.swap) := by
    filter_upwards [continuousAt_fst.eventually hei,continuousAt_snd.eventually hfi] with q hqe hqf
    change cost (riemannianExp x q.2) (riemannianExp x (e q.1))=
      cost (riemannianExp y q.1) (riemannianExp y (f q.2))
    rw [hqe,hqf]
    exact cost_symm _ _
  let S := (ContinuousLinearEquiv.prodComm ℝ W V).toContinuousLinearMap
  have HS := second_fderiv_comp_affine (f := B) S 0 (0:W×V)
    (by simpa [S,B,Prod.swap] using hB2) (d,0) (0,k)
  have H : fderiv ℝ (fderiv ℝ A) (0,0) (d,0) (0,k)=
      fderiv ℝ (fderiv ℝ B) (0,0) (0,d) (k,0) := by
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp only [S,zero_add,map_zero,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.prodComm_apply,Prod.swap_prod_mk,zero_add] at HS
    simpa only [Prod.zero_eq_mk] using HS
  have Hsym := (hB2.isSymmSndFDerivAt (by norm_num)).eq (0,d) (k,0)
  rw [Hsym] at H
  change fderiv ℝ (fderiv ℝ A) (0,0) (d,0) (0,k)=
    fderiv ℝ (fderiv ℝ B) (0,0) (k,0) (0,d) at H
  rw [normalCost_log_mixed he hep,normalCost_log_mixed hf hfq] at H
  exact (neg_injective H).trans (real_inner_comm _ _)

end WeakMTWTransport

end



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

lemma exists_smooth_two_sided_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) ∧
      (∀ᶠ v in 𝓝 p, L (riemannianExp x v)=v) := by
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
  refine ⟨L,hL,hLy,?_,?_⟩
  · have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
      (continuousAt_extChartAt y).eventually (e.open_target.mem_nhds (hep ▸ e.map_source hpe))
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
  · filter_upwards [e.open_source.mem_nhds hpe] with v hv
    change e.symm (d (riemannianExp x v))=v
    rw [←show e v=d (riemannianExp x v) from congrFun he v]
    exact e.left_inv hv

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ReciprocalInverses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma reciprocal_inverses {A R : F →L[ℝ] E} {B L : E →L[ℝ] F}
    (hAB : ∀ d k, inner ℝ (A d) k=inner ℝ d (B k))
    (hAL : ∀ v, A (L v)=v) (hBR : ∀ w, B (R w)=w) (v:E) (w:F) :
    inner ℝ (L v) w=inner ℝ v (R w) := by
  have H := hAB (L v) (R w)
  rw [hAL,hBR] at H
  exact H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpReciprocity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma exists_reciprocal_normal_exp_coordinates {x y : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hp : p∈injectivityDomain x) (hq : q∈injectivityDomain y)
    (hpx : riemannianExp x p=y) (hqy : riemannianExp y q=x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ L p ∧ ContDiffAt ℝ ∞ R q ∧ L p=0 ∧ R q=0 ∧
      (∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v) ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      ∀ v w, inner ℝ (fderiv ℝ L p v) w=inner ℝ v (fderiv ℝ R q w) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨X,hX,hXp,hXi,hXl⟩ := exists_smooth_two_sided_fiber_log hp
  obtain ⟨Y,hY,hYq,hYi,hYl⟩ := exists_smooth_two_sided_fiber_log hq
  obtain ⟨Nx,hNx,hNx0,hNxi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) x)
  obtain ⟨Ny,hNy,hNy0,hNyi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) y)
  rw [hpx] at hX hXp hXi
  rw [hqy] at hY hYq hYi
  simp only [riemannianExp_zero] at hNx hNx0 hNxi hNy hNy0 hNyi
  let e : W → V := fun w => X (riemannianExp y w)
  let f : V → W := fun v => Y (riemannianExp x v)
  let L : V → W := fun v => Ny (riemannianExp x v)
  let R : W → V := fun w => Nx (riemannianExp y w)
  have he : ContDiffAt ℝ ∞ e 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ X (riemannianExp y 0) from
      by simpa only [riemannianExp_zero] using hX).comp 0 (contMDiff_riemannianExp_fiber y 0)).contDiffAt
  have hf : ContDiffAt ℝ ∞ f 0 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,W) ∞ Y (riemannianExp x 0) from
      by simpa only [riemannianExp_zero] using hY).comp 0 (contMDiff_riemannianExp_fiber x 0)).contDiffAt
  have hL : ContDiffAt ℝ ∞ L p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,W) ∞ Ny (riemannianExp x p) from
      by simpa only [hpx] using hNy).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hR : ContDiffAt ℝ ∞ R q :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ Nx (riemannianExp y q) from
      by simpa only [hqy] using hNx).comp q (contMDiff_riemannianExp_fiber y q)).contDiffAt
  have he0 : e 0=p := by dsimp [e]; rw [riemannianExp_zero,hXp]
  have hf0 : f 0=q := by dsimp [f]; rw [riemannianExp_zero,hYq]
  have hLp : L p=0 := by dsimp [L]; rw [hpx,hNy0]
  have hRq : R q=0 := by dsimp [R]; rw [hqy,hNx0]
  have hei : ∀ᶠ w in 𝓝 (0:W), riemannianExp x (e w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) (0:W) from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hXi)
  have hfi : ∀ᶠ v in 𝓝 (0:V), riemannianExp y (f v)=riemannianExp x v :=
    (show ContinuousAt (riemannianExp x) (0:V) from (continuous_riemannianExp x).continuousAt).eventually
      (by simpa only [riemannianExp_zero] using hYi)
  have hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v :=
    (show ContinuousAt (riemannianExp x) p from (continuous_riemannianExp x).continuousAt).eventually
      (by simpa only [hpx] using hNyi)
  have hRi : ∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w :=
    (show ContinuousAt (riemannianExp y) q from (continuous_riemannianExp y).continuousAt).eventually
      (by simpa only [hqy] using hNxi)
  have heL : (fun v => e (L v)) =ᶠ[𝓝 p] (fun v => v) := by
    filter_upwards [hLi,hXl] with v hvi hvl
    change X (riemannianExp y (L v))=v
    rw [hvi]
    exact hvl
  have hfR : (fun w => f (R w)) =ᶠ[𝓝 q] (fun w => w) := by
    filter_upwards [hRi,hYl] with w hwi hwl
    change Y (riemannianExp x (R w))=w
    rw [hwi]
    exact hwl
  have hAL : ∀ v:V, fderiv ℝ e 0 (fderiv ℝ L p v)=v := by
    intro v
    have H := local_inverse_derivative (by simpa only [hLp] using he.differentiableAt (by simp))
      (hL.differentiableAt (by simp)) heL v
    simpa only [hLp] using H
  have hBR : ∀ w:W, fderiv ℝ f 0 (fderiv ℝ R q w)=w := by
    intro w
    have H := local_inverse_derivative (by simpa only [hRq] using hf.differentiableAt (by simp))
      (hR.differentiableAt (by simp)) hfR w
    simpa only [hRq] using H
  refine ⟨L,R,hL,hR,hLp,hRq,hLi,hRi,?_⟩
  exact reciprocal_inverses (normal_log_derivatives_adjoint he hf (he0 ▸ hp) (hf0 ▸ hq) hei hfi) hAL hBR

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_StationarySchur
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma diagonal_stationary_factorization {B : F×E → ℝ} {e : E → F}
    {p : E} {J : E →L[ℝ] F}
    (hB : ContDiffAt ℝ 2 B (e p,p)) (he : HasFDerivAt e J p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ k:E, fderiv ℝ B (e v,v) (0,k)=0)
    (d k:E) :
    fderiv ℝ (fderiv ℝ B) (e p,p) (0,d) (0,k)=
      -fderiv ℝ (fderiv ℝ B) (e p,p) (J d,0) (0,k) := by
  have hd := (((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v => (e v,v)) p
      (he.prodMk (hasFDerivAt_id (𝕜 := ℝ) p))).clm_apply
        (hasFDerivAt_const ((0:F),k) p)
  have hzero : (fun v => fderiv ℝ B (e v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have H := congrArg (fun A : E →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq hzero.symm).unique (hasFDerivAt_const (0:ℝ) p))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,map_zero,
    zero_apply,zero_add,add_apply] at H
  have hdJ : (J d,d)=((J d,0):F×E)+(0,d) := by simp
  rw [hdJ,map_add,add_apply] at H
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinAction_rescale (x : M) {h T : ℝ} (hT : T≠0)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinAction x h T p z = T⁻¹*splitNormalAction x (h/T) (T • p) (z.1,T • z.2) := by
  simp only [fixedJoinAction,splitNormalAction,smul_smul,div_mul_cancel₀ _ hT]
  have he : 1-h/T=(T-h)/T := by field_simp
  rw [he]
  simp only [div_div_eq_mul_div]
  simp only [mul_add]
  congr 1 <;> field_simp [hT]

lemma fixedJoinMiddle_rescale {x : M} {h T : ℝ} (hT : T≠0)
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (splitNormalAction x (h/T) (T • p)) (0,T • p))
    (d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p d k = T*
      fderiv ℝ (fderiv ℝ (splitNormalAction x (h/T) (T • p))) (0,T • p) (0,d) (0,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let L : V×V →L[ℝ] V×V := (ContinuousLinearMap.fst ℝ V V).prod
    (T • ContinuousLinearMap.snd ℝ V V)
  have he : fixedJoinAction x h T p=(fun z => T⁻¹*splitNormalAction x (h/T) (T • p) (L z)) :=
    funext (fixedJoinAction_rescale x hT p)
  rw [fixedJoinMiddle_apply,he,second_fderiv_const_mul]
  have HL := second_fderiv_comp_affine (f := splitNormalAction x (h/T) (T • p)) L 0 (0,p)
    (by simpa [L] using hB) (0,d) (0,k)
  simp only [zero_add] at HL
  rw [HL]
  change T⁻¹*fderiv ℝ (fderiv ℝ (splitNormalAction x (h/T) (T • p))) (0,T • p)
    (0,T • d) (0,T • k)=_
  have he1 (v : V) : ((0:V),T • v)=T • ((0:V),v) := by simp
  simp only [he1,map_smul,smul_apply,smul_eq_mul]
  field_simp [hT]

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FixedJoinSmooth
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

lemma shifted_exp_time (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (h T : ℝ) :
    riemannianExp (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      ((T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)=
      riemannianExp x (T • p) := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale (T-h) (sprayFlow h ⟨x,p⟩))).1=_
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel,riemannianExp_smul]
  rfl

lemma fixedJoinAction_joint_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (TangentSpace 𝓘(ℝ,Model n) x ×
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x)) =>
      fixedJoinAction x h q.1 q.2.1 q.2.2) (T,(p,(0,p))) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let a : ℝ × (V×(V×V)) := (T,(p,(0,p)))
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x q.2.2.1) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.2.2.1) a from by fun_prop).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (h • q.2.2.2)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => h • q.2.2.2) a from by fun_prop).contMDiffAt
  have hw : ContMDiffAt 𝓘(ℝ,ℝ×(V×(V×V))) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ×(V×(V×V)) => riemannianExp x (q.1 • q.2.1)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun q : ℝ×(V×(V×V)) => q.1 • q.2.1) a from by fun_prop).contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,h • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (h • p)) := by
    simpa only [riemannianExp_zero] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (h • p),riemannianExp x (T • p)) := by
    dsimp only at hc₂
    rw [shifted_exp_time] at hc₂
    simpa only [riemannianExp_smul] using hc₂
  exact ((hc₁'.comp a (hu.prodMk hv)).contDiffAt.div_const h).add
    (((hc₂'.comp a (hv.prodMk hw)).contDiffAt).div
      (contDiffAt_fst.sub contDiffAt_const) (sub_ne_zero.mpr hTh))

lemma fixedJoinAction_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hTh : T≠h)
    (hleft : h • p∈injectivityDomain x)
    (hright : (T-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  exact (fixedJoinAction_joint_contDiffAt hTh hleft hright).comp (0,p)
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FixedJoinMiddle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinMiddle_eq_slice {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fderiv ℝ
      (fderiv ℝ (fun b => fixedJoinAction x h T p (0,b))) p v w := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let I : V →L[ℝ] V×V := (0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine (f := fixedJoinAction x h T p) I 0 p
    (by simpa [I] using hB) v w
  simpa [I,fixedJoinMiddle_apply] using H.symm

lemma fixedJoinMiddle_symmetric {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fixedJoinMiddle x h T p w v :=
  (hB.isSymmSndFDerivAt (by norm_num)).eq (0,v) (0,w)

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PrefixAction
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

lemma prefixAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixAction x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalEndpointJoin
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteNormalEndpoint_r9c7d95_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma normalEndpointJoinAction_contDiffAt {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (normalEndpointJoinAction x y h) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  have hP : ContDiffAt ℝ ∞ (fun b : V => cost x (riemannianExp x (h • b))/h) p := by
    have H := (prefixAction_contDiffAt hleft).comp p (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [prefixAction,Function.comp_def,riemannianExp_zero] using H
  have hA : ContMDiffAt 𝓘(ℝ,W×V) 𝓘(ℝ,Model n) ∞
      (fun q : W×V => riemannianExp x (h • q.2)) (0,p) :=
    (contMDiff_riemannianExp_fiber x (h • p)).comp (0,p)
      (((contDiffAt_const (c := h)).smul contDiffAt_snd).contMDiffAt)
  have hB : ContMDiffAt 𝓘(ℝ,W×V) 𝓘(ℝ,Model n) ∞
      (fun q : W×V => riemannianExp y q.1) (0,p) :=
    (contMDiff_riemannianExp_fiber y 0).comp (0,p) contDiffAt_fst.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  dsimp only at hc
  rw [shifted_exp_endpoint,hend] at hc
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (h • p),riemannianExp (n := n) y 0) := by
    simpa only [riemannianExp_smul,riemannianExp_zero] using hc
  exact (hP.comp (0,p) contDiffAt_snd).add ((hc'.comp (0,p) (hA.prodMk hB)).contDiffAt.div_const (1-h))

lemma normalEndpointJoinAction_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hL : ContDiffAt ℝ ∞ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v)
    (d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h 1 p d k=
      -fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p)
        (fderiv ℝ L p d,0) (0,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := normalEndpointJoinAction (n := n) x y h
  have hB := normalEndpointJoinAction_contDiffAt hend hleft hright
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBL : ContDiffAt ℝ 2 B (L p,p) := by simpa only [hLp] using hB2
  have hstat : ∀ᶠ v in 𝓝 p, ∀ k : V, fderiv ℝ B (L v,v) (0,k)=0 := by
    have hmap : ContinuousAt (fun v : V => (L v,v)) p := hL.continuousAt.prodMk continuousAt_id
    have hBn := hmap.eventually ((hBL.of_le (m := 1) (by norm_num)).eventually (by norm_num))
    filter_upwards [split_regular_legs_near hleft hright,hBn,hLi] with v hvreg hvB hvi
    change ContDiffAt ℝ 1 B (L v,v) at hvB
    intro k
    have heq : (fun b => B (L v,b))=(fun b => diagonalSplitAction x h (v,b)) := by
      funext b
      simp only [B,normalEndpointJoinAction,hvi,diagonalSplitAction,splitNormalAction,riemannianExp_zero]
    rw [←fderiv_snd_slice (hvB.differentiableAt (by norm_num)) k,heq,
      fderiv_snd_slice ((diagonalSplitAction_contDiffAt hvreg.1 hvreg.2).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact diagonalSplitAction_stationary hh hh1 hvreg.1 hvreg.2 k
  have hFactor := diagonal_stationary_factorization hBL
    (hL.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt hstat
  have hfixed := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq : (fun b : V => fixedJoinAction x h 1 p (0,b))=(fun b => B (0,b)) := by
    funext b
    simp only [fixedJoinAction,B,normalEndpointJoinAction,riemannianExp_zero,one_smul,hend]
  rw [fixedJoinMiddle_eq_slice hfixed,heq,second_fderiv_snd_slice hB2]
  simpa only [hLp] using hFactor d k

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_EigenOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma bilinearOperator_symmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w:E, B v w=B w v) : (bilinearOperator B).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (bilinearOperator B v) w=inner ℝ v (bilinearOperator B w)
  calc
    _=B v w := bilinearOperator_inner B v w
    _=B w v := hB v w
    _=inner ℝ (bilinearOperator B w) v := (bilinearOperator_inner B w v).symm
    _=inner ℝ v (bilinearOperator B w) := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

local instance tangentFiniteJoin (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

@[simp] lemma fixedJoinOperator_inner (x : M) (h T : ℝ)
    (p d k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (fixedJoinOperator x h T p d) k=fixedJoinMiddle x h T p d k :=
  bilinearOperator_inner _ d k

lemma fixedJoinOperator_symmetric {x:M} {h T:ℝ} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p)) :
    (fixedJoinOperator x h T p).toLinearMap.IsSymmetric :=
  bilinearOperator_symmetric (fixedJoinMiddle_symmetric hB)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MixedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

lemma mixed_factor_adjoint {D : E →L[ℝ] E} {J : E →L[ℝ] F}
    {P : F →L[ℝ] E} (hD : D.toLinearMap.IsSymmetric)
    (hfactor : ∀ v w, inner ℝ (D v) w=inner ℝ (P (J v)) w) :
    D=J.adjoint.comp P.adjoint := by
  ext v
  apply ext_inner_right ℝ
  intro w
  calc
    inner ℝ (D v) w=inner ℝ v (D w) := hD _ _
    _=inner ℝ (D w) v := real_inner_comm _ _
    _=inner ℝ (P (J w)) v := hfactor _ _
    _=inner ℝ (J w) (P.adjoint v) := by
      rw [P.adjoint_inner_right]
    _=inner ℝ (J.adjoint (P.adjoint v)) w := by
      rw [J.adjoint_inner_left,real_inner_comm]
    _=inner ℝ ((J.adjoint.comp P.adjoint) v) w := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianMixedOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section




open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteNormalMixed
local instance endpointProductNormedGroup_r9c7d95_1 (x y : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedAddCommGroup
local instance endpointProductNormedSpace_r9c7d95_1 (x y : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedSpace
local instance endpointDualNormedGroup_r9c7d95_1 (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
local instance endpointDualNormedSpace_r9c7d95_1 (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
lemma normalEndpoint_operator_adjoint_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hL : ContDiffAt ℝ ∞ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v) :
    fixedJoinOperator x h 1 p=(fderiv ℝ L p).adjoint.comp
      (normalEndpointMixedOperator x y h p).adjoint := by
  have hB := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply mixed_factor_adjoint (fixedJoinOperator_symmetric hB)
  intro d k
  rw [fixedJoinOperator_inner,normalEndpointMixedOperator_inner]
  exact normalEndpointJoinAction_factor hh hh1 hend hleft hright hL hLp hLi d k

lemma exists_reverse_exp_fixedJoin_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hp : p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x p=y)
    (hqy : riemannianExp y q=x) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      fixedJoinOperator x h 1 p=(fderiv ℝ R q).comp
        (normalEndpointMixedOperator x y h p).adjoint := by
  obtain ⟨L,R,hL,hR,hLp,hRq,hLi,hRi,hrec⟩ :=
    exists_reciprocal_normal_exp_coordinates hp hq hpx hqy
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) hh hh1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp hh.le hh1
  refine ⟨R,hR,hRq,hRi,?_⟩
  rw [normalEndpoint_operator_adjoint_factor hh hh1 hpx hleft hright hL hLp hLi]
  congr 1
  ext w
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℝ w (fderiv ℝ L p v)=inner ℝ (fderiv ℝ L p v) w := real_inner_comm _ _
    _=inner ℝ v (fderiv ℝ R q w) := hrec v w
    _=inner ℝ (fderiv ℝ R q w) v := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RescaledJoinOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteRescaled_r9c7d95_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma fixedJoinOperator_regular_rescale {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    fixedJoinOperator x h T p=T • fixedJoinOperator x (h/T) 1 (T • p) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  ext d
  apply ext_inner_right ℝ
  intro k
  simp only [smul_apply,real_inner_smul_left,fixedJoinOperator_inner]
  rw [fixedJoinMiddle_rescale hT.ne' hB]
  have H := fixedJoinMiddle_rescale (x := x) (h := h/T) (p := T • p) (T := 1)
    (by norm_num) (by simpa only [Function.comp_def,div_one,one_smul] using hB) d k
  simpa only [div_one,one_smul,one_mul] using congrArg (fun r : ℝ => T*r) H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ReverseIsotropicGain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteReverseGain
lemma exists_reverse_exp_rescaled_fixedJoin_factor_oai {x y : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hhT : h<T) (hp : T • p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x (T • p)=y)
    (hqy : riemannianExp y q=x) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      fixedJoinOperator x h T p=(fderiv ℝ R q).comp
        (T • (normalEndpointMixedOperator x y (h/T) (T • p)).adjoint) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  obtain ⟨R,hR,hRq,hRi,hfac⟩ := exists_reverse_exp_fixedJoin_factor ht ht1 hp hq hpx hqy
  refine ⟨R,hR,hRq,hRi,?_⟩
  rw [fixedJoinOperator_regular_rescale hp hh hhT,hfac]
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,map_smul]

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_reverse_exp_rescaled_fixedJoin_factor_oai.{u_1} := @OAI.WeakMTWTransport.exists_reverse_exp_rescaled_fixedJoin_factor_oai.{u_1}
