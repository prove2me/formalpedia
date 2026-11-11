-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:30:09.889088+00:00
-- url     : https://prove2.me/submissions/3f1ef199-f250-4f69-8543-832abb1c3e99

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
import Definitions.Def_OAIQ232A028
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_normal_relative_hessian_bound
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_outer_true_matrix

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupport
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

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma scalarCostSupport_self (φ : ℝ → ℝ) (v0 : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x) (s : ℝ) :
    scalarCostSupport φ v0 x p s x=φ v0 := by simp [scalarCostSupport]

lemma scalarCostSupport_normal_jet {φ : ℝ → ℝ} {v0 l : ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {s : ℝ} (hs : s≠0)
    (hp : s • p∈injectivityDomain x) (hφ : ContDiffAt ℝ 2 φ v0)
    (hl : deriv φ v0=l) :
    ContDiffAt ℝ 2 (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) 0 ∧
    HasFDerivAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) (innerSL ℝ (l • p)) 0 ∧
    ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      fderiv ℝ (fderiv ℝ (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))) 0 ξ ξ =
        -(l/s)*hessianValue x (s • p) ξ+iteratedDeriv 2 φ v0*(inner ℝ p ξ)^2 := by
  let C := normalCost x (s • p)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x => v0+C 0/s+(-s⁻¹)*C h
  have hf0 : f 0=v0 := by dsimp [f] <;> ring
  have hC : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ContDiffAt ℝ 2 f 0 := contDiffAt_const.add (contDiffAt_const.mul hC)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hp).const_mul (-s⁻¹)).const_add (v0+C 0/s)).congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,inner_neg_left,real_inner_smul_left]
    field_simp
  have he (h : TangentSpace 𝓘(ℝ,Model n) x) :
      scalarCostSupport φ v0 x p s (riemannianExp x h)=φ (f h) := by
    dsimp [scalarCostSupport,f,C,normalCost]
    rw [riemannianExp_zero]
    congr 1
    ring
  have heq : (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))=fun h => φ (f h) := funext he
  rw [heq]
  have hφf : ContDiffAt ℝ 2 φ (f 0) := hf0.symm ▸ hφ
  refine ⟨hφf.comp 0 hf,?_,?_⟩
  · have H := (hφf.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt 0 hD
    rw [hf0,hl] at H
    apply H.congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_smul_left]
  · intro ξ
    rw [second_fderiv_scalar_comp hf hφf ξ,hf0,hl,hD.fderiv]
    have H : fderiv ℝ (fderiv ℝ f) 0 ξ ξ=(-s⁻¹)*hessianValue x (s • p) ξ := by
      have hd : fderiv ℝ f=fun h => (-s⁻¹) • fderiv ℝ C h := by
        funext h
        dsimp only [f]
        rw [fderiv_const_add]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := C) (-s⁻¹)) h
      rw [hd]
      change fderiv ℝ ((-s⁻¹) • fderiv ℝ C) 0 ξ ξ = _
      rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ C) (-s⁻¹)]
      rw [hessianValue_eq_normalHessian hp]
      rfl
    rw [H]
    simp only [innerSL_apply_apply]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchCost2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_cost_branch_with_action (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (z.1,riemannianExp z.1 z.2) ∧
      (∀ᶠ r in 𝓝 z,G (r.1,riemannianExp r.1 r.2)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨P,hP,hPz,hleft,hright⟩ := exists_smooth_exp_branch z hz
  let G : M×M → ℝ := fun q => ‖(P q).2‖^2/2
  refine ⟨G,(contMDiff_tangent_energy (P (z.1,riemannianExp z.1 z.2))).comp _ hP,?_,?_⟩
  · filter_upwards [hleft] with r hr
    change ‖(P (r.1,riemannianExp r.1 r.2)).2‖^2/2=‖r.2‖^2/2
    rw [hr]
  let F : TangentBundle 𝓘(ℝ,Model n) M → M×M := fun r => (r.1,riemannianExp r.1 r.2)
  have hF : Continuous F :=
    ((Bundle.contMDiff_proj (fun v : M => TangentSpace 𝓘(ℝ,Model n) v)).prodMk contMDiff_riemannianExp).continuous
  have hPnear : ∀ᶠ q in 𝓝 (F z), ContinuousAt P q := by
    have hzero : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 0 P (F z) := hP.of_le bot_le
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mp hzero).mono
      (fun point hpoint => hpoint.continuousAt)
  have hRnear : ∀ᶠ q in 𝓝 (F z), ∀ᶠ q' in 𝓝 q,
      (P q').1=q'.1 ∧ riemannianExp (P q').1 (P q').2=q'.2 :=
    eventually_eventually_nhds.mpr hright
  filter_upwards [hleft,(hF.continuousAt.eventually (hPnear.and hRnear))] with r hr hnear
  intro hrID
  have hC : {v : TangentBundle 𝓘(ℝ,Model n) M | v.2 ∈ minimizingVectors v.1} ∈ 𝓝 (P (F r)) := by
    rw [show P (F r)=r from hr]
    exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors r hrID)
  have hmin := hnear.1.preimage_mem_nhds hC
  filter_upwards [hmin,hnear.2] with q hqmin hq
  change dist q.1 q.2^2/2=‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  have hd : dist q.1 q.2=‖(P q).2‖ :=
    (congrArg₂ dist hq.1.symm hq.2.symm).trans hqmin
  rw [hd]
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

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma contMDiff_reverseRay : ContMDiff
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (reverseRay (n := n) (M := M)) := by
  exact contMDiff_tangentScale.comp
    (contMDiff_const.prodMk (contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)))

lemma fiber_nonconjugate_of_smooth_left_inverse
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (P : M×M → TangentBundle 𝓘(ℝ,Model n) M)
    (hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,riemannianExp z.1 z.2))
    (hPz : P (z.1,riemannianExp z.1 z.2)=z)
    (hleft : ∀ᶠ r in 𝓝 z,P (r.1,riemannianExp r.1 r.2)=r) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let V := TangentSpace 𝓘(ℝ,Model n) z.1
  let y := riemannianExp z.1 z.2
  let d := extChartAt 𝓘(ℝ,Model n) y
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : V ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  let f : V → Model n := fun v => d (riemannianExp z.1 v)
  let g : Model n → Model n := fun w => (χ (P (z.1,d.symm w))).2
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d y) :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))
  have hp : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun w => P (z.1,d.symm w)) (d y) := by
    have hm : ContMDiffAt 𝓘(ℝ,Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
        (fun w => (z.1,d.symm w)) (d y) := contMDiffAt_const.prodMk hd
    have hP' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (z.1,d.symm (d y)) := by
      rw [hdy]; exact hP
    exact hP'.comp (d y) hm
  have hχ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n×Model n) ∞ χ (P (z.1,d.symm (d y))) := by
    rw [hdy,hPz]
    exact contMDiffAt_extChartAt
  have hg : ContDiffAt ℝ ∞ g (f z.2) :=
    contDiffAt_snd.comp (f z.2) (hχ.comp (d y) hp).contDiffAt
  have hf : ContDiffAt ℝ ∞ f z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hfiber : Continuous (fun v : V => (⟨z.1,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    (contMDiff_fiber_embedding z.1).continuous
  have hfleft : ∀ᶠ v in 𝓝 z.2,P (z.1,riemannianExp z.1 v)=⟨z.1,v⟩ :=
    hfiber.continuousAt.eventually hleft
  have hsrc : ∀ᶠ v in 𝓝 z.2,riemannianExp z.1 v∈d.source :=
    (continuous_riemannianExp z.1).continuousAt.eventually (extChartAt_source_mem_nhds y)
  have heq : g ∘ f =ᶠ[𝓝 z.2] L := by
    filter_upwards [hfleft,hsrc] with v hv hvs
    change (χ (P (z.1,d.symm (d (riemannianExp z.1 v))))).2=L v
    rw [d.left_inv hvs,hv]
    rfl
  have hD : (fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)=(L : V →L[ℝ] Model n) := by
    rw [←fderiv_comp _ (hg.differentiableAt (by simp)) (hf.differentiableAt (by simp)),
      heq.fderiv_eq,L.fderiv]
  intro u v huv
  apply L.injective
  have H := congrArg (fderiv ℝ g (f z.2)) huv
  change ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) u=
    ((fderiv ℝ g (f z.2)).comp (fderiv ℝ f z.2)) v at H
  rw [hD] at H
  exact H

lemma reverseRay_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp (reverseRay z).1 (reverseRay z).2)
      (riemannianExp (reverseRay z).1 v)) (reverseRay z).2) := by
  obtain ⟨P,hP,hPz,hleft,_⟩ := exists_smooth_exp_branch z hz
  let Q : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => reverseRay (P (q.2,q.1))
  have hQ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Q
      ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) := by
    rw [reverseRay_endpoint,reverseRay_base]
    have hs : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := contMDiffAt_snd.prodMk contMDiffAt_fst
    have hp : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ (fun q : M×M => P (q.2,q.1))
        (riemannianExp z.1 z.2,z.1) := hP.comp (riemannianExp z.1 z.2,z.1) hs
    exact contMDiff_reverseRay.contMDiffAt.comp (riemannianExp z.1 z.2,z.1) hp
  apply fiber_nonconjugate_of_smooth_left_inverse (reverseRay z) Q hQ
  · dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base,hPz]
  · have H := continuous_reverseRay.continuousAt.eventually
      (show ∀ᶠ r in 𝓝 (reverseRay (reverseRay z)),P (r.1,riemannianExp r.1 r.2)=r from
        by rw [reverseRay_involutive]; exact hleft)
    filter_upwards [H] with r hr
    dsimp only [Q]
    rw [reverseRay_endpoint,reverseRay_base] at hr
    rw [hr,reverseRay_involutive]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EndpointLowerJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section EndpointLowerJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma norm_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) :
    ‖(reverseRay z).2‖=‖z.2‖ := by
  change ‖(-1:ℝ) • (sprayFlow 1 z).2‖=‖z.2‖
  rw [neg_one_smul,norm_neg,sprayFlow_speed]

lemma exists_reverse_branch_with_forward_action
    (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        ((reverseRay z).1,riemannianExp (reverseRay z).1 (reverseRay z).2) ∧
      (∀ᶠ r in 𝓝 z,G (riemannianExp r.1 r.2,r.1)=‖r.2‖^2/2) ∧
      ∀ᶠ r in 𝓝 (reverseRay z),r.2∈injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨G,hG,ha,hagree⟩ := exists_smooth_cost_branch_with_action
    (reverseRay z) (reverseRay_nonconjugate z hz)
  refine ⟨G,hG,?_,hagree⟩
  filter_upwards [continuous_reverseRay.continuousAt.eventually ha] with r hr
  rw [norm_reverseRay,reverseRay_endpoint,reverseRay_base] at hr
  exact hr

end EndpointLowerJet
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
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
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
    _ = L v v := by rw [←he]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveBilinearBound
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
open Set Metric

namespace WeakMTWTransport
section PositiveBilinearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bilinear_positive_baseline (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ m>0,∀ v : E,m*‖v‖^2≤B v v := by
  let S := sphere (0:E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hc : ContinuousOn (fun v:E => B v v) S :=
    (B.continuous.clm_apply continuous_id).continuousOn
  obtain ⟨m,hm,Hm⟩ : ∃ m>0,∀ v∈S,m≤B v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨v,hv,Hv⟩ := hS.exists_isMinOn hne hc
      have hn : ‖v‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using hv
      have hp : 0 < B v v := hB v (by intro he; simp [he] at hn)
      exact ⟨B v v,hp,fun w hw => Hv hw⟩
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  exact ⟨m,hm,bilinear_lower_of_unit B (fun v hv => Hm v (by simpa only [S,mem_sphere,dist_zero_right] using hv))⟩

end PositiveBilinearBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma divided_hessian_decrease {a : M} {r ξ : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s<1) :
    hessianValue a (s • r) ξ/s ≤ hessianValue a (t • r) ξ/t := by
  rcases eq_or_lt_of_le hts with h | h
  · simp only [h,le_refl]
  by_cases hξ : ξ=0
  · subst ξ
    rw [hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr (ht.trans h) hs),
      hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr ht (h.trans hs))]
    simp only [map_zero,zero_div,le_refl]
  exact (divided_hessian_strict_decrease hr ht h hs hξ).le

lemma exists_divided_hessian_baseline {a : M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s0 : ℝ} (ht : 0 < t) (hts : t < s0) (hs0 : s0<1) :
    ∃ m>0,∀ s : ℝ,s0 ≤ s → s<1 → ∀ ξ : TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-hessianValue a (s • r) ξ/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := t⁻¹ • normalHessian a (t • r)-s0⁻¹ • normalHessian a (s0 • r)
  have hIDt := contracted_minimizer_mem_injectivityDomain hr ht (hts.trans hs0)
  have hIDs := contracted_minimizer_mem_injectivityDomain hr (ht.trans hts) hs0
  have hB (ξ : TangentSpace 𝓘(ℝ,Model n) a) : B ξ ξ=
      hessianValue a (t • r) ξ/t-hessianValue a (s0 • r) ξ/s0 := by
    rw [hessianValue_eq_normalHessian hIDt,hessianValue_eq_normalHessian hIDs]
    simp only [B,sub_apply,smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,hm,Hm⟩ := exists_bilinear_positive_baseline B (fun ξ hξ => by
    rw [hB]
    exact sub_pos.mpr (divided_hessian_strict_decrease hr ht hts hs0 hξ))
  refine ⟨m,hm,?_⟩
  intro s hss hs1 ξ
  have H := Hm ξ
  rw [hB] at H
  have Hd := divided_hessian_decrease (ξ := ξ) hr (ht.trans hts) hss hs1
  linarith only [H,Hd]

end DividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterSplitLowerTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section OuterSplitLowerTest
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma outer_split_lower_test {v : M → ℝ} {a : M}
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (v a))
    {l : ℝ} (hd : HasDerivAt φ l (v a)) (hl : l≠0)
    (hmount : ∀ y : M,φ (v a)+cost a (riemannianExp a r)-cost y (riemannianExp a r)≤φ (v y))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ f : TangentSpace 𝓘(ℝ,Model n) a → ℝ, ContDiffAt ℝ 2 f 0 ∧ f 0=v a ∧
      (∀ᶠ h in 𝓝 0,f h≤v (riemannianExp a h)) ∧
      fderiv ℝ f 0=innerSL ℝ (l⁻¹ • r) ∧
      ∀ ξ,fderiv ℝ (fderiv ℝ f) 0 ξ ξ=
        -(l*s)⁻¹*hessianValue a (s • r) ξ-
          (iteratedDeriv 2 φ (v a)/l^3)*(inner ℝ r ξ)^2 := by
  let : Nonempty M := ⟨a⟩
  let F : TangentSpace 𝓘(ℝ,Model n) a → ℝ := fun h =>
    scalarCostSupport id (φ (v a)) a r s (riemannianExp a h)
  have hsp := contracted_minimizer_mem_injectivityDomain hr hs hs1
  obtain ⟨hF,hDF,hHF⟩ := scalarCostSupport_normal_jet (φ := id) (v0 := φ (v a))
    (l := 1) hs.ne' hsp contDiffAt_id (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD : fderiv ℝ F 0=innerSL ℝ r := by simpa only [one_smul] using hDF.fderiv
  have hFv : F 0=φ (v (riemannianExp a (0 : TangentSpace 𝓘(ℝ,Model n) a))) := by
    simp only [F,riemannianExp_zero,scalarCostSupport_self,id_eq]
  have hlo : ∀ᶠ h in 𝓝 0,F h≤φ (v (riemannianExp a h)) := by
    apply Filter.Eventually.of_forall
    intro h
    have H := hmount (riemannianExp a h)
    have Hs := minimizing_split_upper_support hr hs hs1 (riemannianExp a h)
    have He := minimizing_split_contact hr hs hs1
    dsimp only [F,scalarCostSupport,id_eq]
    linarith only [H,Hs,He]
  obtain ⟨f,hf,hfv,hfl,hfd,hfh⟩ := scalar_inverse_lower_test hmono
    (v := fun h => v (riemannianExp a h)) (x := 0)
    (by simpa only [riemannianExp_zero] using hφ)
    (by simpa only [riemannianExp_zero] using hd) hl hF hFv hlo
  refine ⟨f,hf,by simpa only [riemannianExp_zero] using hfv,hfl,?_,?_⟩
  · rw [hfd,hD,map_smul]
  · intro ξ
    rw [hfh,hD]
    have H := hHF ξ
    change fderiv ℝ (fderiv ℝ F) 0 ξ ξ=_ at H
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id',deriv_const,zero_mul,add_zero,one_div] at H
    rw [H,riemannianExp_zero,innerSL_apply_apply]
    ring

end OuterSplitLowerTest
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_OuterNonconjugacy
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
section OuterNonconjugacy
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_nonconjugate (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {x0 a : M}
    {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (uv.1 a))
    {l : ℝ} (hd : HasDerivAt φ l (uv.1 a)) (hl : 1 < l)
    (hconc : iteratedDeriv 2 φ (uv.1 a) ≤ 0)
    (hmount : ∀ y : M,φ (uv.1 a)+cost a (riemannianExp a r)-cost y (riemannianExp a r) ≤ φ (uv.1 y)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp a r) (riemannianExp a v)) r) := by
  have hlp : 0 < l := zero_lt_one.trans hl
  have ht : 0 < l⁻¹ := inv_pos.mpr hlp
  have ht1 : l⁻¹ < 1 := (inv_lt_one₀ hlp).mpr hl
  let s0 := (l⁻¹+1)/2
  have hts : l⁻¹ < s0 := by dsimp [s0]; linarith only [ht1]
  have hs0 : s0 < 1 := by dsimp [s0]; linarith only [ht1]
  have hp := contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  obtain ⟨C,hC,HC⟩ := hmtw.exists_normal_relative_hessian_bound hlam hcap hp (div_pos hm hlp)
  let D := fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp a r) (riemannianExp a v)) r
  have hz (ξ : TangentSpace 𝓘(ℝ,Model n) a) (hξ : D ξ=0) : ξ=0 := by
    by_contra hne
    have hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) a) 𝓘(ℝ,Model n)
        (riemannianExp a) r ξ=0 := by rw [exp_mfderiv_apply_eq_coordinate]; exact hξ
    have H := conjugate_radial_hessian_tendsto_atBot hr hk (inner_self_ne_zero.mpr hne)
    let A := hessianValue a (l⁻¹ • r) ξ
    let K := |A|+C*‖ξ‖^2
    have hK : 0 ≤ K := add_nonneg (abs_nonneg A) (mul_nonneg hC (sq_nonneg _))
    have hb := H.eventually (eventually_lt_atBot (-l*K-1))
    have hn : ∀ᶠ s : ℝ in 𝓝[<] 1,s0 ≤ s ∧ s < 1 :=
      (((eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)).and self_mem_nhdsWithin
    obtain ⟨s,hs,hlt⟩ := (hn.and hb).exists
    have hsp : 0 < s := ht.trans_le (hts.le.trans hs.1)
    obtain ⟨f,hf,hfv,hflo,hfD,hfH⟩ := outer_split_lower_test hr hmono hφ hd hlp.ne' hmount hsp hs.2
    have hscalar (d : TangentSpace 𝓘(ℝ,Model n) a) :
        0 ≤ -(iteratedDeriv 2 φ (uv.1 a)/l^3)*(inner ℝ r d)^2 :=
      mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (pow_nonneg hlp.le _))) (sq_nonneg _)
    have hpos (d : TangentSpace 𝓘(ℝ,Model n) a) :
        (m/l)*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ f) 0 d d+hessianValue a (l⁻¹ • r) d := by
      rw [hfH]
      have Hbase := mul_le_mul_of_nonneg_left (Hm s hs.1 hs.2 d) ht.le
      have Halgebra : l⁻¹*(hessianValue a (l⁻¹ • r) d/l⁻¹-hessianValue a (s • r) d/s)=
          -(l*s)⁻¹*hessianValue a (s • r) d+hessianValue a (l⁻¹ • r) d := by
        field_simp
        ring
      rw [Halgebra] at Hbase
      have HP := hscalar d
      simp only [div_eq_mul_inv] at Hbase HP ⊢
      nlinarith only [Hbase,HP]
    have HB := HC x0 uv huv f hf hfD hfv.symm hflo hpos ξ
    rw [hfH] at HB
    have HA : -A ≤ |A| := neg_le_abs A
    have HS := hscalar ξ
    have Hbound : -hessianValue a (s • r) ξ/(l*s) ≤ K := by
      dsimp [A,K] at *
      simp only [mul_inv_rev,div_eq_mul_inv] at *
      nlinarith only [HB,HA,HS]
    have Hmul := (div_le_iff₀ (mul_pos hlp hsp)).mp Hbound
    have Hls : l*s ≤ l := by nlinarith only [hs.2,hlp]
    have Hmul' := mul_le_mul_of_nonneg_left Hls hK
    linarith only [Hmul,Hmul',hlt]
  intro p q hpq
  apply sub_eq_zero.mp
  apply hz (p-q)
  rw [map_sub,hpq,sub_self]

end OuterNonconjugacy
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BranchDividedBaseline
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section BranchDividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_hessian_inward_limit {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (ξ : TangentSpace 𝓘(ℝ,Model n) a) :
    Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
      (𝓝 (fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ)) := by
  have H := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have HH := (H.2.2 ξ).div (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
    (𝓝 ((fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a ((1:ℝ) • r))))) 0 ξ ξ / 1)) at HH
  simpa only [one_smul,div_one] using HH

lemma exists_branch_divided_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t:ℝ} (ht : 0 < t) (ht1 : t < 1)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ m>0,∀ ξ:TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-
        fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ := by
  let s0 := (t+1)/2
  have hts : t < s0 := by dsimp [s0] <;> linarith
  have hs0 : s0 < 1 := by dsimp [s0] <;> linarith
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  refine ⟨m,hm,?_⟩
  intro ξ
  have H := ((tendsto_const_nhds (x := hessianValue a (t • r) ξ/t)).sub (cost_branch_hessian_inward_limit hr hG hagree ξ))
  apply ge_of_tendsto H
  filter_upwards [(eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  exact Hm s hs.le hs1 ξ

end BranchDividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ParametricActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ParametricActive
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma activeLogs_iff_minimum {v:M → ℝ} (hv:Continuous v) {x:M}
    {p:TangentSpace 𝓘(ℝ,Model n) x} : p∈activeLogs v x ↔
    p∈minimizingVectors x ∧ ∀ y:M,v (riemannianExp x p)+cost x (riemannianExp x p) ≤ v y+cost x y := by
  constructor
  · rintro ⟨hm,hcontact⟩
    refine ⟨hm,fun y=>?_⟩
    have H:=cTransform_gap_nonneg hv x y
    dsimp only [contactGap] at *
    linarith only [H,hcontact]
  · rintro ⟨hm,hmin⟩
    refine ⟨hm,?_⟩
    obtain ⟨y,hy⟩:=cTransform_gap_zero hv x
    have H:=cTransform_gap_nonneg hv x (riemannianExp x p)
    have HH:=hmin y
    dsimp only [contactGap] at *
    linarith only [H,HH,hy]

end ParametricActive
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ActiveOuter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.active_outer_nonconjugate (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {φ:ℝ → ℝ} (hφc:Continuous φ) (hmono:StrictMono φ)
    {z:TangentBundle 𝓘(ℝ,Model n) M}
    (ha:z.2∈activeLogs (φ ∘ uv.2) z.1)
    (hφ:ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)))
    {l:ℝ} (hd:HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2))) (hl:1 < l)
    (hconc:iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0) :
    Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2) := by
  let w:=reverseRay z
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have hnorm (y:M):uv.2 x0+vu.1 y=uv.2 y := by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hbase:uv.2 x0+vu.1 w.1=uv.2 (riemannianExp z.1 z.2) := by
    rw [hnorm,show w.1=riemannianExp z.1 z.2 from reverseRay_base z]
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 w.1) := by
    exact (hbase.symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hψD:HasDerivAt ψ l (vu.1 w.1) := by
    have hd':HasDerivAt φ l (uv.2 x0+vu.1 w.1) := hbase.symm ▸ hd
    have H:=hd'.comp (vu.1 w.1) ((hasDerivAt_id (vu.1 w.1)).const_add (uv.2 x0))
    simpa only [mul_one,Function.comp_def,ψ] using H
  have hψC:iteratedDeriv 2 ψ (vu.1 w.1) ≤ 0 := by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [hbase]
    exact hconc
  have hψmono:StrictMono ψ := fun _ _ h=>hmono (by linarith)
  have hm:∀y:M,ψ (vu.1 w.1)+cost w.1 (riemannianExp w.1 w.2)-
      cost y (riemannianExp w.1 w.2) ≤ ψ (vu.1 y) := by
    intro y
    have H:=((activeLogs_iff_minimum (hφc.comp uv.2.continuous)).mp ha).2 y
    dsimp only [Function.comp_apply] at H
    dsimp only [ψ]
    rw [hnorm,hnorm,show riemannianExp w.1 w.2=z.1 from reverseRay_endpoint z,
      show w.1=riemannianExp z.1 z.2 from reverseRay_base z,cost_symm _ z.1,cost_symm y z.1]
    linarith only [H]
  have H:=hmtw.modified_outer_nonconjugate hlam hcap (densityDualClass_reverse hlam huv)
    (reverseRay_minimizing ha.1) hψmono hψ hψD hl hψC hm
  have H':=reverseRay_nonconjugate w H
  have hw:reverseRay w=z := reverseRay_involutive z
  rw [hw] at H'
  exact H'

end ActiveOuter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_OuterActiveMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterActiveMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance oamFinite_r16e834_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance oamComplete_r16e834_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
lemma WeakMTW.exists_uniform_active_outer_matrix_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
      ∀ (z:TangentBundle 𝓘(ℝ,Model n) M) (l:ℝ),z.2∈activeLogs (φ ∘ uv.2) z.1 →
      ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
      HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
      iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
      ∀ B:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (riemannianExp z.1 (z.2+d)))+‖z.2+d‖^2/2) 0 B →
      ∃V:TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0  <  inner ℝ (V d) d) ∧
        (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
          (inner ℝ z.2 d)^2  ≤  inner ℝ (V d) d) ∧
        0 < expJacobian (n:=n) z.1 z.2 ∧
        0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
        expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det  ≤
          l^n*K*(expJacobian (n:=n) z.1 z.2)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_true_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv φ huv hφc hm z l ha hφ hd hl hconc B hBs hB hjet
  have hnc:=hmtw.active_outer_nonconjugate hlam hcap huv hφc hm ha hφ hd hl hconc
  obtain ⟨G,hG,hact,hagree⟩:=exists_reverse_branch_with_forward_action z hnc
  have hy:riemannianExp z.1 z.2=(reverseRay z).1:=(reverseRay_base z).symm
  have hx:riemannianExp (reverseRay z).1 (reverseRay z).2=z.1:=reverseRay_endpoint z
  have hr:=(reverseRay_minimizing ha.1)
  have hact':∀ᶠ q in 𝓝 z.2,G (riemannianExp z.1 q,z.1)=‖q‖^2/2:=
    (FiberBundle.continuous_totalSpaceMk (Model n)
      (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x) z.1).continuousAt.eventually hact
  obtain ⟨C,V,hCI,hCd,hpair,hVs,hVp,hVeq,hVdet⟩:=HK z.1 (reverseRay z).1 z.2
    (reverseRay z).2 G l hy hx hr hnc (by simpa only [hx] using hG) hact' hagree hl
    x0 uv φ huv hm (by simpa only [reverseRay_base] using hφ)
    (by simpa only [reverseRay_base] using hd) (by simpa only [reverseRay_base] using hconc)
    B hBs hB hjet
  have hl0:0 < l:=zero_lt_one.trans hl
  obtain ⟨m,hm',HM⟩:=exists_branch_divided_baseline hr (inv_pos.mpr hl0)
    (inv_lt_one_of_one_lt₀ hl) hG hagree
  have hJac:0 < expJacobian (n:=n) z.1 z.2:=by
    rw [←hCd]
    apply lt_of_le_of_ne (LinearMap.normDet_nonneg _)
    apply Ne.symm
    rw [ne_eq,LinearMap.normDet_eq_zero_iff_ker_ne_bot,not_not,LinearMap.ker_eq_bot]
    exact hCI
  refine ⟨V,hVs,hVp,?_,hJac,?_,hVdet⟩
  · intro d
    have HH:=HM (C d)
    rw [div_inv_eq_mul,mul_comm (hessianValue _ _ _) l,hx] at HH
    have H0:0 ≤ l*hessianValue (reverseRay z).1 (l⁻¹ • (reverseRay z).2) (C d)-
        fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp (reverseRay z).1 w,z.1))) 0 (C d) (C d):=
      (mul_nonneg hm'.le (sq_nonneg _)).trans HH
    rw [hVeq,hy]
    linarith only [H0]
  · exact expJacobian_pos_of_injectivityDomain
      (contracted_minimizer_mem_injectivityDomain hr (inv_pos.mpr hl0) (inv_lt_one_of_one_lt₀ hl))
end OuterActiveMatrix
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix_oai.{u_1}
