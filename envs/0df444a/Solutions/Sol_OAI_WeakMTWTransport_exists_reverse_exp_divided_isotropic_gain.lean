-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:50.113504+00:00
-- url     : https://prove2.me/submissions/9895b03b-bcbc-445e-8811-8cda622f59a9

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_reverse_exp_rescaled_fixedJoin_factor

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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_joining_selector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : p∈injectivityDomain x) (ht : 0 < t) (ht1 : t < 1) :
    ∃ b : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ b 0 ∧ b 0=p ∧
      (∀ᶠ a in 𝓝 0, normalCost x p a=splitNormalAction x t p (a,b a)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let y := riemannianExp x p
  obtain ⟨P,hP,hP0,_,hPinv⟩ := exists_smooth_exp_branch z
    (riemannianExp_interior_nonconjugate hp)
  let Q : V → TangentBundle 𝓘(ℝ,Model n) M := fun a => P (riemannianExp x a,y)
  have hQ0 : Q 0=z := by dsimp [Q]; rw [riemannianExp_zero]; exact hP0
  have hmap : ContMDiffAt 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun a : V => (riemannianExp x a,y)) 0 :=
    (contMDiff_riemannianExp_fiber x 0).prodMk contMDiffAt_const
  have hQ : ContMDiffAt 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Q 0 := by
    exact (show ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (riemannianExp x (0:V),y) from by
        simpa only [riemannianExp_zero] using hP).comp 0 hmap
  let Z : V → M := fun a => (sprayFlow t (Q a)).1
  have hZ : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞ Z 0 :=
    (Bundle.contMDiff_proj (fun w : M => TangentSpace 𝓘(ℝ,Model n) w)).contMDiffAt.comp 0
      (contMDiff_sprayFlow.contMDiffAt.comp 0 (contMDiffAt_const.prodMk hQ))
  have hZ0 : Z 0=riemannianExp x (t • p) := by
    dsimp only [Z]; rw [hQ0]; exact (riemannianExp_smul x p t).symm
  have hpre := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  obtain ⟨L,hL,hL0,hLinv⟩ := exists_smooth_fiber_log hpre
  let b : V → V := fun a => t⁻¹ • L (Z a)
  have hb : ContDiffAt ℝ ∞ b 0 :=
    ((contDiffAt_const (c := t⁻¹)).smul ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (Z 0) from
      hZ0 ▸ hL).comp 0 hZ).contDiffAt)
  have hb0 : b 0=p := by simp only [b,hZ0,hL0,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  refine ⟨b,hb,hb0,?_⟩
  have hQmin : ∀ᶠ a in 𝓝 (0:V), (Q a).2∈injectivityDomain (Q a).1 :=
    hQ.continuousAt.eventually (show {r : TangentBundle 𝓘(ℝ,Model n) M |
      r.2∈injectivityDomain r.1}∈𝓝 (Q 0) from by
        rw [hQ0]; exact isOpen_total_injectivityDomain.mem_nhds hp)
  have hQi : ∀ᶠ a in 𝓝 (0:V), (Q a).1=riemannianExp x a ∧
      riemannianExp (Q a).1 (Q a).2=y := by
    have H := hmap.continuousAt.eventually (show ∀ᶠ w in 𝓝 (riemannianExp x (0:V),y),
      (P w).1=w.1 ∧ riemannianExp (P w).1 (P w).2=w.2 from by
        simpa only [riemannianExp_zero] using hPinv)
    exact H
  have hZi : ∀ᶠ a in 𝓝 (0:V), riemannianExp x (t • b a)=Z a := by
    have H := hZ.continuousAt.eventually (show ∀ᶠ w in 𝓝 (Z 0), riemannianExp x (L w)=w from
      hZ0 ▸ hLinv)
    simpa only [b,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using H
  filter_upwards [hQmin,hQi,hZi] with a ha hi hz
  have H := splitNormalAction_contact (injectivityDomain_subset_minimizingVectors _ ha) ht ht1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at H
  rw [riemannianExp_smul] at H
  change cost (Q a).1 (Z a)/t+cost (Z a) (riemannianExp (Q a).1 (Q a).2)/(1-t)=
    cost (Q a).1 (riemannianExp (Q a).1 (Q a).2) at H
  rw [hi.2,hi.1] at H
  change cost (riemannianExp x a) y =
    cost (riemannianExp x a) (riemannianExp x (t • b a))/t+
      cost (riemannianExp x (t • b a)) y/(1-t)
  rw [hz]
  exact H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_EnvelopePole
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma upper_contact_fderiv {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hle : f ≤ᶠ[𝓝 x] g) (heq : f x=g x) : fderiv ℝ f x=fderiv ℝ g x := by
  have hmin : IsLocalMin (g-f) x := by
    filter_upwards [hle] with y hy
    change g x-f x≤g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  exact (sub_eq_zero.mp H).symm

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

lemma stationary_contact_hessian {B : E×E → ℝ} {f : E → ℝ}
    {b : E → E} {x q : E} {R : E →L[ℝ] E}
    (hB : ContDiffAt ℝ 2 B (x,q)) (hb : HasFDerivAt b R x) (hb0 : b x=q)
    (hf : ∀ᶠ a in 𝓝 x, DifferentiableAt ℝ f a)
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1 ≤ B z)
    (heq : ∀ᶠ a in 𝓝 x, f a=B (a,b a)) :
    HasFDerivAt (fderiv ℝ f)
      ((fderiv ℝ (fderiv ℝ B) (x,q)).comp
        ((ContinuousLinearMap.id ℝ E).prod R) |>.flip |>.comp
          ((ContinuousLinearMap.id ℝ E).prod 0) |>.flip) x := by
  let I : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod 0
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod R
  let G : E → E →L[ℝ] ℝ := fun a => (fderiv ℝ B (a,b a)).comp I
  have hmap := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk hb
  have hB' : ContDiffAt ℝ 2 B (x,b x) := by rwa [hb0]
  have hG := (((hB'.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a => (a,b a)) x hmap).clm_comp
      (hasFDerivAt_const I x)
  have he : fderiv ℝ f =ᶠ[𝓝 x] G := by
    have hn := hmap.continuousAt.eventually (hB'.eventually (by norm_num))
    have hln : ∀ᶠ a in 𝓝 x, ∀ᶠ z in 𝓝 (a,b a), f z.1 ≤ B z :=
      hmap.continuousAt.eventually (eventually_eventually_nhds.mpr (by simpa [hb0] using hle))
    filter_upwards [hf,heq,hn,hln] with a hfa hea hBa hla
    have ha : ContinuousAt (fun v : E => (v,b a)) a := by fun_prop
    have hlocal : ∀ᶠ v in 𝓝 a, f v ≤ B (v,b a) := ha.eventually hla
    have hd := (hBa.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (v,b a)) a
      ((hasFDerivAt_id a).prodMk (hasFDerivAt_const (b a) a))
    exact (upper_contact_fderiv hfa hd.differentiableAt hlocal hea).trans hd.fderiv
  apply (hG.congr_of_eventuallyEq he).congr_fderiv
  ext d e
  simp only [hb0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_zero,
    zero_apply,zero_add,I]

lemma stationary_graph_middle_equation {B : E×E → ℝ}
    {b : E → E} {x q : E} {R : E →L[ℝ] E}
    (hB : ContDiffAt ℝ 2 B (x,q)) (hb : HasFDerivAt b R x) (hb0 : b x=q)
    (hstat : ∀ᶠ a in 𝓝 x, ∀ k : E, fderiv ℝ B (a,b a) (0,k)=0)
    (hmix : ∀ d k:E, fderiv ℝ (fderiv ℝ B) (x,q) (d,0) (0,k)= -inner ℝ d k)
    (d k:E) : fderiv ℝ (fderiv ℝ B) (x,q) (0,R d) (0,k)=inner ℝ d k := by
  have hB' : ContDiffAt ℝ 2 B (x,b x) := by rwa [hb0]
  have hd := (((hB'.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a => (a,b a)) x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk hb)).clm_apply
        (hasFDerivAt_const ((0:E),k) x)
  have he : (fun a => fderiv ℝ B (a,b a) (0,k)) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have H := congrArg (fun A : E →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const (0:ℝ) x))
  simp only [hb0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,map_zero,
    zero_apply,zero_add,add_apply] at H
  have hdR : (d,R d)=((d,0):E×E)+(0,R d) := by simp
  rw [hdR,map_add,add_apply,hmix] at H
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SplitActionSchur
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

lemma splitNormalAction_schur_equality {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : p∈injectivityDomain x) (ht : 0 < t) (ht1 : t < 1) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      (∀ d k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p)
        (0,R d) (0,k)=inner ℝ d k) ∧
      (∀ d, hessianValue x p d=hessianValue x (t • p) d/t-inner ℝ (R d) d) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := splitNormalAction x t p
  obtain ⟨b,hb,hb0,hcontact⟩ := exists_smooth_joining_selector hp ht ht1
  let R := fderiv ℝ b 0
  have hbd : HasFDerivAt b R 0 := (hb.differentiableAt (by simp)).hasFDerivAt
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc : ContDiffAt ℝ ∞ B (0,p) :=
    (splitNormalAction_contDiffAt hleft hright).comp (f := fun z : V×V => (p,z))
      (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ᶠ a in 𝓝 (0:V), DifferentiableAt ℝ (normalCost x p) a :=
    ((normalCost_contDiffAt hp).of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num) |>.mono
      (fun _ h => h.differentiableAt (by norm_num))
  have hle : ∀ᶠ z in 𝓝 ((0:V),p), normalCost x p z.1 ≤ B z :=
    Eventually.of_forall (fun z => normalCost_le_splitNormalAction x p z.1 z.2 ht ht1)
  have hstat : ∀ᶠ a in 𝓝 (0:V), ∀ k : V, fderiv ℝ B (a,b a) (0,k)=0 := by
    have hmap := (hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk hbd
    have hBnear : ∀ᶠ a in 𝓝 (0:V), DifferentiableAt ℝ B (a,b a) := by
      have HC : ContDiffAt ℝ 1 B (0,b 0) := by rw [hb0]; exact hBc.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      exact (hmap.continuousAt.eventually (HC.eventually (by norm_num))).mono
        (fun _ h => h.differentiableAt (by norm_num))
    filter_upwards [hBnear,hcontact] with a ha hc
    intro k
    have hlocal : IsLocalMin (fun v : V => B (a,v)) (b a) := by
      apply Filter.Eventually.of_forall
      intro v
      change splitNormalAction x t p (a,b a) ≤ splitNormalAction x t p (a,v)
      rw [←hc]
      exact normalCost_le_splitNormalAction x p a v ht ht1
    have hd := ha.hasFDerivAt.comp (f := fun v : V => (a,v)) (b a)
      ((hasFDerivAt_const a (b a)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (b a)))
    have H := congrArg (fun A : V →L[ℝ] ℝ => A k) (hd.fderiv.symm.trans hlocal.fderiv_eq_zero)
    change fderiv ℝ B (a,b a) (0,k)=0 at H
    exact H
  have hmix (d k : V) : fderiv ℝ (fderiv ℝ B) (0,p) (d,0) (0,k)= -inner ℝ d k := by
    rw [splitNormalAction_mixed_pairing ht.ne' hleft hright,real_inner_comm]
  refine ⟨R,stationary_graph_middle_equation hB hbd hb0 hstat hmix,?_⟩
  intro d
  have HH := stationary_contact_hessian hB hbd hb0 hf hle hcontact
  have HE := congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ => A d d) HH.fderiv
  change normalHessian x p d d = fderiv ℝ (fderiv ℝ B) (0,p) (d,R d) (d,0) at HE
  have hsplit : (d,R d)=((d,0):V×V)+(0,R d) := by simp
  rw [hsplit,map_add,add_apply,(hB.isSymmSndFDerivAt (by norm_num)).eq (0,R d) (d,0),hmix] at HE
  rw [←splitTrialValue_eq_hessian hleft hright,splitTrialValue_source] at HE
  rw [hessianValue_eq_normalHessian hp,HE,real_inner_comm d (R d)]
  ring

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

lemma fixedJoinAction_schur {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      (∀ d k, fixedJoinMiddle x h T p (R d) k=inner ℝ d k) ∧
      (∀ d, hessianValue x (T • p) d/T=hessianValue x (h • p) d/h-inner ℝ (R d) d) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  obtain ⟨R,hR,hA⟩ := splitNormalAction_schur_equality hp ht ht1
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨T⁻¹ • R,?_,?_⟩
  · intro d k
    rw [smul_apply,map_smul,smul_apply,
      fixedJoinMiddle_rescale hT.ne' hB,hR]
    simp [smul_eq_mul,hT.ne']
  · intro d
    have HA := hA d
    rw [smul_smul,div_mul_cancel₀ _ hT.ne'] at HA
    rw [HA,smul_apply,real_inner_smul_left]
    field_simp

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

lemma fixedJoinMiddle_symmetric {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p v w=fixedJoinMiddle x h T p w v :=
  (hB.isSymmSndFDerivAt (by norm_num)).eq (0,v) (0,w)

end

lemma fixedJoinMiddle_one_nonneg {x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hh : 0<h) (hh1 : h<1)
    (hp : p∈minimizingVectors x) (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ fixedJoinMiddle x h 1 p v v := by
  have HB := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (p,z))
    (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have HB2 := HB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := fixedJoinMiddle_rescale (x := x) (h := h) (p := p) (T := 1)
    (by norm_num) (by simpa only [Function.comp_def,div_one,one_smul] using HB2) v v
  simp only [div_one,one_smul,one_mul] at H
  rw [H,←splitTrialValue_eq_hessian hleft hright]
  exact splitTrialValue_nonneg hh hh1 hp hleft hright

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

lemma inverse_of_bilinear_pairing {B : E →L[ℝ] E →L[ℝ] ℝ} {R : E →L[ℝ] E}
    (hR : ∀ v w:E, B (R v) w=inner ℝ v w) (v:E) : bilinearOperator B (R v)=v := by
  exact ext_inner_right ℝ (fun w => by rw [bilinearOperator_inner,hR])
variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma left_inverse_of_right_inverse {D R : E →L[ℝ] E}
    (hDR : ∀ v:E, D (R v)=v) (v:E) : R (D v)=v := by
  have hsurj : Function.Surjective D := fun w => ⟨R w,hDR w⟩
  have hinj : Function.Injective D := D.toLinearMap.injective_iff_surjective.mpr hsurj
  apply hinj
  exact hDR (D v)

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

omit [CompleteSpace E] [CompleteSpace F] in
lemma factor_surjective_of_right_inverse [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {D S : E →L[ℝ] E} {J : F →L[ℝ] E} {C : E →L[ℝ] F}
    (hdim : finrank ℝ E=finrank ℝ F)
    (hDS : ∀ v, D (S v)=v) (hD : ∀ v, D v=J (C v)) :
    Function.Surjective C := by
  have hDin : Function.Injective D := D.toLinearMap.injective_iff_surjective.mpr
    (fun v => ⟨S v,hDS v⟩)
  have hCin : Function.Injective C := by
    intro v w hvw
    apply hDin
    rw [hD,hD,hvw]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := C.toLinearMap)).mp hCin

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

local instance tangentFiniteRescaled_ra31757_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma fixedJoinAction_regular_contDiffAt {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    ContDiffAt ℝ ∞ (fixedJoinAction x h T p) (0,p) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : V×V => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  change ContDiffAt ℝ ∞ (splitNormalAction x (h/T) (T • p)) (0,T • p) at hBc
  have H := hBc.comp (f := fun z : V×V => (z.1,T • z.2)) (0,p)
    (contDiffAt_fst.prodMk ((contDiffAt_const (c := T)).smul contDiffAt_snd))
  have heq : fixedJoinAction x h T p=(fun z : V×V =>
      T⁻¹*splitNormalAction x (h/T) (T • p) (z.1,T • z.2)) :=
    funext (fixedJoinAction_rescale x hT.ne' p)
  rw [heq]
  exact contDiffAt_const.mul H

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

lemma fixedJoinOperator_regular_nonneg {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ inner ℝ (fixedJoinOperator x h T p v) v := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  have hmin := injectivityDomain_subset_minimizingVectors x hp
  have hleft := contracted_minimizer_mem_injectivityDomain hmin ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  rw [fixedJoinOperator_regular_rescale hp hh hhT,
    smul_apply,real_inner_smul_left,fixedJoinOperator_inner]
  exact mul_nonneg hT.le (fixedJoinMiddle_one_nonneg ht ht1 hmin hleft hright v)

lemma fixedJoinOperator_inverse_nonneg {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T)
    (hDR : ∀ v, fixedJoinOperator x h T p (R v)=v)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : 0 ≤ inner ℝ (R v) v := by
  have H := fixedJoinOperator_regular_nonneg hp hh hhT (R v)
  rw [hDR,real_inner_comm] at H
  exact H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_InverseDifferenceGain
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_difference_pullback_identity {D B R S : E →L[ℝ] E}
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v) (w : E) :
    inner ℝ (R (D w)-S (D w)) (D w)=
      inner ℝ ((D-B) w) w+inner ℝ (R ((D-B) w)) ((D-B) w) := by
  have hRB := left_inverse_of_right_inverse hBR
  have hRw : R (D w)-S (D w)=R ((D-B) w) := by
    simp only [sub_apply,map_sub,hDS,hRB]
  rw [hRw]
  have hsplit : D w=B w+(D-B) w := by simp
  conv_lhs => rhs; rw [hsplit]
  rw [inner_add_right]
  have H : inner ℝ (R ((D-B) w)) (B w)=inner ℝ ((D-B) w) w := by
    calc
      _ = inner ℝ (B (R ((D-B) w))) w := (hB _ _).symm
      _ = _ := congrArg (fun v => inner ℝ v w) (hBR ((D-B) w))
  rw [H]

lemma inverse_difference_pullback_lower {D B R S : E →L[ℝ] E} {c : ℝ}
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v)
    (hR : ∀ v, 0≤ inner ℝ (R v) v)
    (hcross : ∀ v, c*‖v‖^2≤ inner ℝ ((D-B) v) v) (w : E) :
    c*‖w‖^2≤ inner ℝ (R (D w)-S (D w)) (D w) := by
  rw [inverse_difference_pullback_identity hB hBR hDS]
  exact (hcross w).trans (le_add_of_nonneg_right (hR _))

lemma inverse_difference_isotropic_of_factor
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {D B R S : E →L[ℝ] E} {J : F →L[ℝ] E} {C : E →L[ℝ] F} {a c : ℝ}
    (ha : 0<a) (hc : 0 ≤ c)
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v)
    (hR : ∀ v, 0≤ inner ℝ (R v) v)
    (hcross : ∀ v, c*‖v‖^2≤ inner ℝ ((D-B) v) v)
    (hfactor : ∀ v, D v=J (C v)) (hC : Function.Surjective C)
    (hbound : ∀ v, ‖C v‖≤a*‖v‖) (w : F) :
    (c/a^2)*‖w‖^2≤ inner ℝ (R (J w)-S (J w)) (J w) := by
  obtain ⟨v,rfl⟩ := hC w
  have H := inverse_difference_pullback_lower hB hBR hDS hR hcross v
  rw [hfactor v] at H
  apply le_trans _ H
  have hn : ‖C v‖^2≤a^2*‖v‖^2 := by
    nlinarith only [hbound v,sq_nonneg (a*‖v‖-‖C v‖),norm_nonneg (C v),
      mul_nonneg ha.le (norm_nonneg v)]
  calc
    (c/a^2)*‖C v‖^2≤(c/a^2)*(a^2*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hc (sq_nonneg a))
    _=c*‖v‖^2 := by field_simp

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
lemma exists_reverse_exp_divided_isotropic_gain_oai {x y : M} {h s t a c : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hhs : h < s) (hht : h<t)
    (hps : s • p∈injectivityDomain x) (hpt : t • p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x (s • p)=y)
    (hqy : riemannianExp y q=x) (ha : 0<a) (hc : 0 ≤ c)
    (hcross : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
      c*‖v‖^2≤fixedJoinMiddle x h s p v v-fixedJoinMiddle x h t p v v)
    (hbound : s*‖normalEndpointMixedOperator x y (h/s) (s • p)‖≤a) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
        (c/a^2)*‖w‖^2 ≤ hessianValue x (s • p) (fderiv ℝ R q w)/s-
          hessianValue x (t • p) (fderiv ℝ R q w)/t := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  let D := fixedJoinOperator x h s p
  let B := fixedJoinOperator x h t p
  let C := s • (normalEndpointMixedOperator x y (h/s) (s • p)).adjoint
  have hs : 0 < s := hh.trans hhs
  obtain ⟨R,hR,hRq,hRi,hfactor⟩ := exists_reverse_exp_rescaled_fixedJoin_factor hh hhs hps hq hpx hqy
  obtain ⟨S,hDS,hAs⟩ := fixedJoinAction_schur hps hh hhs
  obtain ⟨U,hBU,hAt⟩ := fixedJoinAction_schur hpt hh hht
  have hDs : ∀ v:V, D (S v)=v := fun v => inverse_of_bilinear_pairing hDS v
  have hBu : ∀ v:V, B (U v)=v := fun v => inverse_of_bilinear_pairing hBU v
  have hBs : B.toLinearMap.IsSymmetric := fixedJoinOperator_symmetric
    ((fixedJoinAction_regular_contDiffAt hpt hh hht).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hUn : ∀ v:V, 0 ≤ inner ℝ (U v) v :=
    fixedJoinOperator_inverse_nonneg hpt hh hht hBu
  have hfac : ∀ v:V, D v=fderiv ℝ R q (C v) := fun v =>
    congrArg (fun A : V →L[ℝ] V => A v) hfactor
  have hCs : Function.Surjective C := factor_surjective_of_right_inverse
    (show finrank ℝ V=finrank ℝ W from rfl) hDs hfac
  have hCn : ‖C‖≤a := by
    dsimp only [C]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,LinearIsometryEquiv.norm_map]
    exact hbound
  have hC : ∀ v:V, ‖C v‖≤a*‖v‖ := fun v =>
    (C.le_opNorm v).trans (mul_le_mul_of_nonneg_right hCn (norm_nonneg v))
  have hcross' : ∀ v:V, c*‖v‖^2≤ inner ℝ ((D-B) v) v := by
    intro v
    simpa only [sub_apply,inner_sub_left,D,B,fixedJoinOperator_inner]
      using hcross v
  refine ⟨R,hR,hRq,hRi,?_⟩
  intro w
  have H := inverse_difference_isotropic_of_factor ha hc hBs hBu
    (left_inverse_of_right_inverse hDs) hUn hcross' hfac hCs hC w
  rw [inner_sub_left] at H
  linarith only [H,hAs (fderiv ℝ R q w),hAt (fderiv ℝ R q w)]

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain_oai.{u_1} := @OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain_oai.{u_1}
