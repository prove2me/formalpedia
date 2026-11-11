-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:43.491711+00:00
-- url     : https://prove2.me/submissions/79a82c88-5c4b-4f29-9686-4dc9b3bab4fa

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
import Definitions.Def_OAIQ232A024
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_active_outer_matrix

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bilinear_isBigO_norm_mul {α : Type*} (L : Filter α)
    (B : E →L[ℝ] F →L[ℝ] G) (u : α → E) (v : α → F) :
    (fun x => B (u x) (v x)) =O[L] (fun x => ‖u x‖*‖v x‖) := by
  apply Asymptotics.IsBigO.of_bound ‖B‖
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_assoc] using B.le_opNorm₂ (u x) (v x))

lemma bilinear_remainder_of_hasFDerivAt {a : E → F} {A : E →L[ℝ] F}
    (ha : HasFDerivAt a A 0) (ha0 : a 0=0) (B : F →L[ℝ] F →L[ℝ] ℝ) :
    (fun h => B (a h) (a h)-B (A h) (A h)) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have hR : (fun h => a h-A h) =o[𝓝 0] (fun h : E => h) := by
    simpa only [zero_add,ha0,sub_zero] using hasFDerivAt_iff_isLittleO_nhds_zero.mp ha
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  have hA : (fun h : E => A h) =O[𝓝 0] (fun h => h) := A.isBigO_id _
  have h1 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => a h-A h) a).trans_isLittleO
    (hR.norm_left.norm_right.mul_isBigO hO.norm_left.norm_right)
  have h2 := (bilinear_isBigO_norm_mul (𝓝 (0:E)) B (fun h => A h) (fun h => a h-A h)).trans_isLittleO
    (hA.norm_left.norm_right.mul_isLittleO hR.norm_left.norm_right)
  have he : (fun h => B (a h) (a h)-B (A h) (A h)) =
      (fun h => B (a h-A h) (a h)+B (A h) (a h-A h)) := by
    funext h
    simp only [map_sub,_root_.sub_apply]
    ring
  rw [he]
  simpa only [pow_two] using h1.add h2

end WeakMTWTransport

end

end OAI
end

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LowerTaylorComposition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasLowerSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasLowerSecondTaylor (fun h => f (a h)) 0 (pullBilinear B A) := by
  have hO : a =O[𝓝 0] (fun h : E => h) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub
  obtain ⟨C,hC,HC⟩ := hO.exists_pos
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  intro ε hε
  have hδ : 0 < ε/(2*C^2) := div_pos hε (by positivity)
  have hB := (bilinear_remainder_of_hasFDerivAt ha ha0 B).def hε
  filter_upwards [ht.eventually (hf _ hδ),HC.bound,hB] with h hh haB hb
  simp only [zero_apply,add_zero] at hh ⊢
  rw [ha0,pullBilinear_apply]
  have hb' : |B (a h) (a h)-B (A h) (A h)| ≤ ε*‖h‖^2 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb
  have hsq : ‖a h‖^2 ≤ C^2*‖h‖^2 := by
    nlinarith only [sq_nonneg (C*‖h‖-‖a h‖),haB,norm_nonneg (a h),
      mul_nonneg hC.le (norm_nonneg h)]
  have hsq' := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have he : ε/(2*C^2)*(C^2*‖h‖^2)=(ε/2)*‖h‖^2 := by
    field_simp [hC.ne']
  rw [he] at hsq'
  linarith only [hh,(abs_le.mp hb').1,hsq']

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FixedJoinSpectrum
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
open scoped Topology ContDiff

namespace WeakMTWTransport
section FixedJoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

local instance tangentFiniteSpectrum_r49b8a5_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma tangent_finrank (x : M) : finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)=n :=
  finrank_euclideanSpace_fin
end FixedJoinSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PrefixAction
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

lemma prefixAction_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    prefixAction x t (0,p)=t*(‖p‖^2/2) := by
  have hm := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p))=‖t • p‖ at hm
  simp only [prefixAction,riemannianExp_zero,cost,hm,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  by_cases ht : t=0
  · simp [ht]
  · field_simp

lemma prefixAction_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    (fun v => prefixAction x t (0,v)) =ᶠ[𝓝 p] (fun v => t*(‖v‖^2/2)) := by
  have hn : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    (continuous_const_smul t).continuousAt.eventually ((isOpen_injectivityDomain x).mem_nhds hp)
  filter_upwards [hn] with v hv
  exact prefixAction_axis hv

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PullbackDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

lemma abs_det_hessian_pullback (B:E →L[ℝ] F) (W:F →L[ℝ] F)
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) :
    |(B.adjoint.comp (W.comp B)).det|=B.toLinearMap.normDet^2*|W.det| := by
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap W.toLinearMap hd
  have h2:=LinearMap.normDet_comp_of_finrank_eq (W.comp B).toLinearMap B.adjoint.toLinearMap hd
  have h3:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap B.adjoint.toLinearMap hd
  have hs:(B.adjoint.comp B).det=B.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using B.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at h2 h3
  change |(B.adjoint.comp B).det|=B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet at h3
  rw [hs,abs_of_nonneg (sq_nonneg _)] at h3
  rw [LinearMap.normDet_eq_abs_det] at h1
  change |(B.adjoint.comp (W.comp B)).det|=_ at h2
  rw [h2]
  change B.adjoint.toLinearMap.normDet*(W.comp B).toLinearMap.normDet=_
  rw [show (W.comp B).toLinearMap.normDet=|W.det| *B.toLinearMap.normDet from h1]
  calc
    _ = (B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet)*|W.det| := by ring
    _ = _ := by rw [←h3]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

lemma det_positive_hessian_pullback {B:E →L[ℝ] F} {W:F →L[ℝ] F}
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) (hi:Function.Injective B)
    (hW:∀x y,inner ℝ (W x) y=inner ℝ x (W y))
    (hp:∀x,x≠0 → 0 < inner ℝ (W x) x) {l:ℝ} (hl:0<l) :
    (∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d) ∧
    (l • (B.adjoint.comp (W.comp B))).det=
      l^Module.finrank ℝ E*B.toLinearMap.normDet^2*W.det := by
  have hs:∀x y,inner ℝ ((l • (B.adjoint.comp (W.comp B))) x) y=
      inner ℝ x ((l • (B.adjoint.comp (W.comp B))) y):=by
    intro x y
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hW]
  have hpos:∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d := by
    intro d hd
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    exact mul_pos hl (hp _ (fun h=>hd (hi (h.trans B.map_zero.symm))))
  refine ⟨hpos,?_⟩
  have H:=abs_det_hessian_pullback B W hd
  have hpull:0<(B.adjoint.comp (W.comp B)).det:=by
    apply symmetric_det_pos
    · intro x y
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_right,hW]
    · intro d hd
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
      exact hp _ (fun h=>hd (hi (h.trans B.map_zero.symm)))
  rw [abs_of_pos hpull,abs_of_pos (symmetric_det_pos hW hp)] at H
  change (l • (B.adjoint.comp (W.comp B)).toLinearMap).det=_
  rw [LinearMap.det_smul]
  change l^Module.finrank ℝ E*(B.adjoint.comp (W.comp B)).det=_
  rw [H]
  ring
end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
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

lemma movingPrefixEnergy_axis_near {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    (movingPrefixEnergy a t b)=ᶠ[𝓝 p]
      (fun q=>t*(‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) q‖^2/2)) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  filter_upwards [(L.continuous.tendsto p).eventually (prefixAction_axis_near hp)] with q hq
  simpa only [movingPrefixEnergy,movingNormal_zero hb,movingPrefix_eq hb,
    prefixAction,riemannianExp_zero] using hq

lemma movingPrefixEnergy_hessian {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (movingPrefixEnergy a t b)) p d e=
      t*inner ℝ
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) d)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) e) := by
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  rw [((movingPrefixEnergy_axis_near hb hp).fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [second_fderiv_const_mul]
  have H := second_fderiv_comp_affine (f := fun q=>‖q‖^2/2) L 0 p
    ((half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) d e
  simpa only [zero_add,half_norm_sq_second_fderiv,innerSL_apply_apply,smul_apply,
    smul_eq_mul] using congrArg (fun r:ℝ=>t*r) H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma frameMetric_apply {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (d e:Model n) :
    frameMetric a b d e=inner ℝ (chartFiberInverse a b d) (chartFiberInverse a b e) := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  simpa only [frameMetric,chartFiberInverse,one_mul] using movingPrefixEnergy_hessian hb hp d e

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartOuterMatrix
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
section ChartOuterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance chartOuterFinite (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance chartOuterComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

lemma WeakMTW.exists_uniform_chart_outer_matrix_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → Continuous φ → StrictMono φ →
      ∀ (a:M) (b p:Model n),b∈(extChartAt 𝓘(ℝ,Model n) a).target →
      let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,chartFiberInverse a b p⟩
      ∀ l:ℝ,z.2∈activeLogs (φ ∘ uv.2) z.1 →
      ContDiffAt ℝ 2 φ (uv.2 (riemannianExp z.1 z.2)) →
      HasDerivAt φ l (uv.2 (riemannianExp z.1 z.2)) → 1 < l →
      iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2)) ≤ 0 →
      ∀ B:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0 ≤ B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (movingNormal a (b,p+d)))+
        ‖chartFiberInverse a b (p+d)‖^2/2) 0 B →
      ∃V:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,B d d-(iteratedDeriv 2 φ (uv.2 (riemannianExp z.1 z.2))/l^2)*
          (frameMetric a b p d)^2 ≤ inner ℝ (V d) d) ∧
        0 < expJacobian (n:=n) z.1 z.2 ∧
        0 < expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2) ∧
        expJacobian (n:=n) (reverseRay z).1 (l⁻¹ • (reverseRay z).2)*V.det ≤
          (chartFiberInverse a b).toLinearMap.normDet^2*l^n*K*(expJacobian (n:=n) z.1 z.2)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_active_outer_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv φ huv hφ hm a b p hb z l ha hφ2 hd hl hconc B hBs hB hjet
  let x:M:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let T:=trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx:x∈T.baseSet:=by
    simpa only [x,T,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  let e:=T.continuousLinearEquivAt ℝ x hx
  let A:=chartFiberInverse a b
  have hAe:(A:Model n → TangentSpace 𝓘(ℝ,Model n) x)=e.symm:=
    (T.symm_continuousLinearEquivAt_eq hx).symm
  have hEA (d:Model n):e (A d)=d:=by rw [hAe]; exact e.apply_symm_apply d
  have hAE (d:TangentSpace 𝓘(ℝ,Model n) x):A (e d)=d:=by rw [hAe]; exact e.symm_apply_apply d
  let C:=pullBilinear B e.toContinuousLinearMap
  have hC:HasLowerSecondTaylor (fun d:TangentSpace 𝓘(ℝ,Model n) x=>
      φ (uv.2 (riemannianExp x (A p+d)))+‖A p+d‖^2/2) 0 C:=by
    convert hjet.comp_stationary e.hasFDerivAt e.map_zero using 1
    all_goals try with_reducible_and_instances rfl
    funext d
    simp only [movingNormal_eq hb,map_add]
    change φ (uv.2 (riemannianExp x (A p+d)))+‖A p+d‖^2/2=
      φ (uv.2 (riemannianExp x (A p+A (e d))))+‖A p+A (e d)‖^2/2
    rw [hAE]
  obtain ⟨V,hVs,hVp,hgain,hσ,hσs,hdet⟩:=HK x0 uv φ huv hφ hm z l ha hφ2 hd hl hconc
    C (fun d f=>hBs _ _) (fun d=>hB _) hC
  let W:=A.adjoint.comp (V.comp A)
  have hdim:Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x):=by
    rw [tangent_finrank,finrank_euclideanSpace_fin]
  have hP:=det_positive_hessian_pullback (B:=A) (W:=V) hdim
    (chartFiberInverse_injective hb) hVs hVp (show (0:ℝ)<1 by norm_num)
  simp only [one_smul,one_pow,one_mul] at hP
  refine ⟨W,?_,hP.1,?_,hσ,hσs,?_⟩
  · intro d f
    simp only [W,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hVs]
  · intro d
    have H:=hgain (A d)
    simpa only [C,pullBilinear_apply,ContinuousLinearEquiv.coe_coe,hEA,
      frameMetric_apply hb,W,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left] using H
  · change _*(A.adjoint.comp (V.comp A)).det≤_
    rw [hP.2]
    have H:=mul_le_mul_of_nonneg_left hdet (sq_nonneg A.toLinearMap.normDet)
    nlinarith only [H]
end ChartOuterMatrix
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix_oai.{u_1}
