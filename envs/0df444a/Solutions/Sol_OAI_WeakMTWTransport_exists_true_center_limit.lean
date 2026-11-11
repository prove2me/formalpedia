-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_true_center_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:20:25.024441+00:00
-- url     : https://prove2.me/submissions/ea5855ad-3852-49b5-a4ca-b09668480b00

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
import Definitions.Def_OAIQ232A025
import Theorems.Thm_OAI_WeakMTWTransport_continuous_expJacobian
import Theorems.Thm_OAI_WeakMTWTransport_exists_true_center_jet_gain

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearClose
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

lemma bilinear_quadratic_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (d:E) : |A d d|≤‖A‖*‖d‖^2 := by
  calc
    |A d d| = ‖A d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A d‖*‖d‖ := (A d).le_opNorm d
    _ ≤ (‖A‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (A.le_opNorm d) (norm_nonneg d)
    _ = ‖A‖*‖d‖^2 := by ring

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symmetric_bilinear_norm_bound {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C:ℝ} (hC:0≤C)
    (hbound:∀d,|B d d|≤C*‖d‖^2) : ‖B‖≤C := by
  let T:=bilinearOperator B
  have hT:T.IsSymmetric := bilinearOperator_symmetric hB
  have hn:‖T‖≤C := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro d
    by_cases hd:d=0
    · simpa [hd,ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hC
    · have hp:0<‖d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [T,bilinearOperator_inner,RCLike.re_to_real]
      rw [abs_div,abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      exact hbound d
  apply B.opNorm_le_bound hC
  intro d
  apply (B d).opNorm_le_bound (mul_nonneg hC (norm_nonneg d))
  intro e
  calc
    ‖B d e‖ = ‖inner ℝ (T d) e‖ := by simp only [T,bilinearOperator_inner]
    _ ≤ ‖T d‖*‖e‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖*‖d‖)*‖e‖ := mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg e)
    _ ≤ (C*‖d‖)*‖e‖ := by gcongr

attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactDualSpace
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactGroup
attribute [local instance] OAI.WeakMTWTransport.bilinearCompactSpace
omit [CompleteSpace E] in
lemma exists_bilinear_limit [FiniteDimensional ℝ E]
    {Bj:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖Bj j‖≤C) :
    ∃B:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (Bj ∘ σ) atTop (𝓝 B) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨B,hB,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => Bj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨B,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end BilinearCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace WeakMTWTransport
section BilinearMatrix
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearMatrix_det (B:E →L[ℝ] E →L[ℝ] ℝ) :
    (bilinearMatrix B).det=(bilinearOperator B).det := by
  exact LinearMap.det_toMatrix _ _

lemma bilinearMatrix_quad (B:E →L[ℝ] E →L[ℝ] ℝ)
    (v:Fin (Module.finrank ℝ E) → ℝ) :
    v ⬝ᵥ (bilinearMatrix B *ᵥ v)=
      B ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v)
        ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v) := by
  let b:=stdOrthonormalBasis ℝ E
  let w:=b.toBasis.equivFun.symm v
  have hv: (fun i=>b.repr w i)=v:=by
    change b.toBasis.equivFun (b.toBasis.equivFun.symm v)=v
    exact b.toBasis.equivFun.apply_symm_apply v
  have hm:bilinearMatrix B *ᵥ v=(fun i=>b.repr (bilinearOperator B w) i):=by
    rw [←hv]
    exact (bilinearOperator B).toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis w
  rw [hm]
  nth_rw 1 [←hv]
  have H:=b.repr.inner_map_map (bilinearOperator B w) w
  rw [bilinearOperator_inner] at H
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using H

lemma bilinearMatrix_nonneg {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d) :
    (bilinearMatrix B).PosSemidef := by
  apply (LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℝ E)).2
  exact (LinearMap.isPositive_iff _).2 ⟨bilinearOperator_symmetric hs,by
    intro d
    change 0 ≤ inner ℝ (bilinearOperator B d) d
    rw [bilinearOperator_inner]
    exact hp d⟩

lemma bilinear_positive_of_det_ne_zero {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d)
    (hd:(bilinearOperator B).det≠0) : ∀d,d≠0 → 0 < B d d := by
  have HM: (bilinearMatrix B).PosDef:=(bilinearMatrix_nonneg hs hp).posDef_iff_det_ne_zero.mpr
    (by rwa [bilinearMatrix_det])
  intro d hd0
  let b:=(stdOrthonormalBasis ℝ E).toBasis
  have hv:b.equivFun d≠0:=by
    intro H
    apply hd0
    exact b.equivFun.injective (by simpa only [map_zero] using H)
  have H:=HM.dotProduct_mulVec_pos hv
  simpa only [star_trivial,bilinearMatrix_quad,b,LinearEquiv.symm_apply_apply] using H

lemma bilinear_det_nonneg {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d) :
    0 ≤ (bilinearOperator B).det := by
  rw [←bilinearMatrix_det]
  exact (bilinearMatrix_nonneg hs hp).det_nonneg

lemma bilinearOperator_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>bilinearOperator (B i)) l (𝓝 (bilinearOperator B₀)) := by
  have hc:Continuous (fun B:E →L[ℝ] E →L[ℝ] ℝ=>bilinearOperator B):=
    continuous_const.clm_comp continuous_id
  exact hc.continuousAt.tendsto.comp hB

lemma bilinear_det_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>(bilinearOperator (B i)).det) l (𝓝 (bilinearOperator B₀).det) := by
  exact ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp (bilinearOperator_tendsto hB)

end BilinearMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingHessianLimit
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
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_clm_apply {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℝ] F} {v : ι → E} {A₀ : E →L[ℝ] F} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i=>A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hc : Continuous (fun q:(E →L[ℝ] F)×E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A₀,v₀)).comp (hA.prodMk_nhds hv)

lemma bilinear_limit_nonneg {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d:E,0≤B i d d) (d:E) :
    0≤B₀ d d := by
  exact ge_of_tendsto (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d))

lemma bilinear_limit_symm {ι : Type*} {l : Filter ι} [NeBot l]
    {B : ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Tendsto B l (𝓝 B₀)) (hp : ∀ᶠ i in l,∀ d e:E,B i d e=B i e d) (d e:E) :
    B₀ d e=B₀ e d := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (tendsto_clm_apply (tendsto_clm_apply hB tendsto_const_nhds) tendsto_const_nhds)
    (hp.mono (fun i hi=>hi d e))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterDetCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section CenterDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.WeakMTWTransport.centerDetDualGroup
attribute [local instance] OAI.WeakMTWTransport.centerDetDualSpace
local instance centerDetBilinearGroup_r8a5371_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance centerDetBilinearSpace_r8a5371_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma exists_center_matrix_limit {V C:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {C₀:E →L[ℝ] E →L[ℝ] ℝ} {a:ℕ → ℝ} {a₀ k₀:ℝ}
    (hC:Tendsto C atTop (𝓝 C₀)) (ha:Tendsto a atTop (𝓝 a₀)) (hk:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k₀ ≤ a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧ (∀d,V₀ d d ≤ C₀ d d) ∧
      0<a₀ ∧ k₀ ≤ a₀*(bilinearOperator V₀).det := by
  have hCn : Tendsto (fun j => ‖C j‖) atTop (𝓝 ‖C₀‖) := hC.norm
  have hCb:∀ᶠ j in atTop,‖C j‖≤‖C₀‖+1:=by
    filter_upwards [hCn.eventually (gt_mem_nhds (show ‖C₀‖<‖C₀‖+1 by linarith))] with j hj
    exact hj.le
  have hbound:∀ᶠ j in atTop,‖V j‖≤‖C₀‖+1:=by
    filter_upwards [hCb,hV] with j hj hv
    apply symmetric_bilinear_norm_bound hv.1 (by positivity)
    intro d
    rw [abs_of_nonneg (hv.2.1 d)]
    calc
      V j d d ≤ C j d d:=hv.2.2.1 d
      _ ≤ |C j d d|:=le_abs_self _
      _ ≤ ‖C j‖*‖d‖^2:=bilinear_quadratic_norm_bound _ _
      _ ≤ (‖C₀‖+1)*‖d‖^2:=mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  obtain ⟨V₀,σ,hσ,HV⟩:=exists_bilinear_limit hbound
  have hve:=hσ.tendsto_atTop.eventually hV
  have hvs:∀d e,V₀ d e=V₀ e d:=bilinear_limit_symm HV (hve.mono (fun j hj=>hj.1))
  have hvp:∀d,0≤V₀ d d:=bilinear_limit_nonneg HV (hve.mono (fun j hj=>hj.2.1))
  have hae:0≤a₀:=ge_of_tendsto (ha.comp hσ.tendsto_atTop) (hve.mono (fun j hj=>hj.2.2.2.1))
  have hdet:k₀≤a₀*(bilinearOperator V₀).det:=ge_of_tendsto
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV)) (hve.mono (fun j hj=>hj.2.2.2.2))
  have hdp:0 < (bilinearOperator V₀).det:=by
    have H:=bilinear_det_nonneg hvs hvp
    nlinarith only [hk,hdet,hae,H]
  have hap:0<a₀:=by nlinarith only [hk,hdet,hae,hdp]
  refine ⟨V₀,σ,hσ,HV,hvs,bilinear_positive_of_det_ne_zero hvs hvp hdp.ne',?_,hap,hdet⟩
  intro d
  exact le_of_tendsto_of_tendsto
    (tendsto_clm_apply (tendsto_clm_apply HV tendsto_const_nhds) tendsto_const_nhds)
    (tendsto_clm_apply (tendsto_clm_apply (hC.comp hσ.tendsto_atTop) tendsto_const_nhds) tendsto_const_nhds)
    (hve.mono (fun j hj=>hj.2.2.1 d))

lemma exists_center_matrix_limit_variable {V C:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {C₀:E →L[ℝ] E →L[ℝ] ℝ} {a k:ℕ → ℝ} {a₀ k₀:ℝ}
    (hC:Tendsto C atTop (𝓝 C₀)) (ha:Tendsto a atTop (𝓝 a₀))
    (hk:Tendsto k atTop (𝓝 k₀)) (hk0:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k j ≤ a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧ (∀d,V₀ d d ≤ C₀ d d) ∧
      0<a₀ ∧ k₀ ≤ a₀*(bilinearOperator V₀).det := by
  have HV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k₀/2 ≤ a j*(bilinearOperator (V j)).det:=by
    filter_upwards [hV,hk.eventually (lt_mem_nhds (show k₀/2<k₀ by linarith))] with j hj hkj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hkj.le.trans hj.2.2.2.2⟩
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,_⟩:=
    exists_center_matrix_limit hC ha (half_pos hk0) HV
  refine ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,?_⟩
  exact le_of_tendsto_of_tendsto (hk.comp hσ.tendsto_atTop)
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV))
    ((hσ.tendsto_atTop.eventually hV).mono (fun j hj=>hj.2.2.2.2))
end CenterDetCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearGainLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearGainLimit
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.gainDualGroup
attribute [local instance] OAI.WeakMTWTransport.gainDualSpace
local instance gainBilinearGroup_r8a5371_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gainBilinearSpace_r8a5371_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma rankForm_tendsto {f:ℕ → E →L[ℝ] ℝ} {g:E →L[ℝ] ℝ}
    (hf:Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j=>(f j).smulRight (f j)) atTop (𝓝 (g.smulRight g)) :=
  (isBoundedBilinearMap_smulRight.continuous.continuousAt.tendsto).comp (hf.prodMk_nhds hf)

variable [FiniteDimensional ℝ E]

lemma exists_bilinear_gain_limit {V H G:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {H₀ G₀:E →L[ℝ] E →L[ℝ] ℝ} {f:ℕ → E →L[ℝ] ℝ} {f₀:E →L[ℝ] ℝ}
    {a k b c:ℕ → ℝ} {a₀ k₀ b₀ c₀:ℝ}
    (hH:Tendsto H atTop (𝓝 H₀)) (hG:Tendsto G atTop (𝓝 G₀))
    (hf:Tendsto f atTop (𝓝 f₀))
    (ha:Tendsto a atTop (𝓝 a₀)) (hk:Tendsto k atTop (𝓝 k₀))
    (hb:Tendsto b atTop (𝓝 b₀)) (hc:Tendsto c atTop (𝓝 c₀)) (hk0:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧ (∀d,V j d d+b j*G j d d+c j*(f j d)^2≤H j d d) ∧
      0≤a j ∧ k j≤a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧
      (∀d,V₀ d d+b₀*G₀ d d+c₀*(f₀ d)^2≤H₀ d d) ∧
      0<a₀ ∧ k₀≤a₀*(bilinearOperator V₀).det := by
  let C:=fun j=>H j-b j • G j-c j • (f j).smulRight (f j)
  let C₀:=H₀-b₀ • G₀-c₀ • f₀.smulRight f₀
  have hC:Tendsto C atTop (𝓝 C₀):=(hH.sub (hb.smul hG)).sub (hc.smul (rankForm_tendsto hf))
  have Hvc:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧ (∀d,V j d d≤C j d d) ∧
      0≤a j ∧ k j≤a j*(bilinearOperator (V j)).det:=by
    filter_upwards [hV] with j hj
    refine ⟨hj.1,hj.2.1,?_,hj.2.2.2⟩
    intro d
    have HH:=hj.2.2.1 d
    simp only [C,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    nlinarith only [HH]
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,hdet⟩:=
    exists_center_matrix_limit_variable hC ha hk hk0 Hvc
  refine ⟨V₀,σ,hσ,HV,hVs,hVp,?_,ha0,hdet⟩
  intro d
  have HH:=hVC d
  simp only [C₀,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul] at HH
  nlinarith only [HH]
end BilinearGainLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
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
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
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

lemma movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (Function.uncurry (movingPrefix a t)) (b,p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp (b,p)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul t)).contMDiffAt

lemma movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixEnergy a t)) (b,p) := by
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q:Model n×Model n=> movingNormal a (q.1,0)) (b,p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp (b,p)
      (contDiffAt_fst.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb] using hC
  exact ((hC'.comp (b,p) (hA.prodMk (movingPrefix_contMDiffAt hb))).contDiffAt.div_const t)

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterRayLimit
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
section CenterRayLimit
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartRay_at_center (c:M) (r:Model n) :
    chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r=⟨c,r⟩ := by
  simp only [chartRay,chartFiberInverse_at_center]
  exact congrArg (fun y:M=>(⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M))
    ((extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c))

lemma chartRay_tendsto {c:M} {b r:ℕ → Model n} {r0:Model n}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) :
    Tendsto (fun k=>chartRay c (b k) (r k)) atTop
      (𝓝 (⟨c,r0⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨c,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hc:extChartAt 𝓘(ℝ,Model n) c c∈(extChartAt 𝓘(ℝ,Model n) c).target:=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have ht:(extChartAt 𝓘(ℝ,Model n) c c,r0)∈χ.target:=
    (tangent_chart_target_iff _ _).mpr hc
  have H: Tendsto (fun k=>χ.symm (b k,r k)) atTop
      (𝓝 (χ.symm (extChartAt 𝓘(ℝ,Model n) c c,r0))):=
    (continuousAt_extChartAt_symm'' ht).tendsto.comp (hb.prodMk_nhds hr)
  rw [tangent_chart_symm_trivialization hc] at H
  change Tendsto _ _ (𝓝 (chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r0)) at H
  rw [chartRay_at_center] at H
  apply H.congr'
  filter_upwards [hb.eventually ((isOpen_extChartAt_target _).mem_nhds hc)] with k hk
  exact tangent_chart_symm_trivialization hk

end CenterRayLimit
end WeakMTWTransport

end
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

omit [Nonempty M] in
lemma frameMetric_continuousAt {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) : ContinuousAt (frameMetric a) b := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  have H := (ContDiffAt.partial_snd_fderiv_two (movingPrefixEnergy_contDiffAt hb hp)).continuousAt
  exact ContinuousAt.comp (f := fun z:Model n=>(z,(0:Model n))) H
    (show ContinuousAt (fun z:Model n=>(z,(0:Model n))) b from
    continuousAt_id.prodMk continuousAt_const)

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameDet
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
section FrameDet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.frameDetFinite
attribute [local instance] OAI.WeakMTWTransport.frameDetComplete
lemma frameMetric_operator {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    bilinearOperator (frameMetric a b)=(chartFiberInverse a b).adjoint.comp (chartFiberInverse a b) := by
  apply ContinuousLinearMap.ext
  intro d
  apply ext_inner_right ℝ
  intro e
  rw [bilinearOperator_inner,frameMetric_apply hb]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

lemma frameMetric_det {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (bilinearOperator (frameMetric a b)).det=(chartFiberInverse a b).toLinearMap.normDet^2 := by
  rw [frameMetric_operator hb]
  simpa only [RCLike.ofReal_real_eq_id,id_eq] using (chartFiberInverse a b).normDet_sq.symm

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma frameNormDet_pos {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    0<(chartFiberInverse a b).toLinearMap.normDet := by
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm _)
  intro h
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h)
    (LinearMap.ker_eq_bot.mpr (chartFiberInverse_injective hb))

lemma frameNormDet_continuousAt {a:M} {b:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContinuousAt (fun z=>(chartFiberInverse a z).toLinearMap.normDet) b := by
  have H:ContinuousAt (fun z=>Real.sqrt (bilinearOperator (frameMetric a z)).det) b := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (bilinear_det_tendsto (frameMetric_continuousAt hb).tendsto)
  apply H.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target _).mem_nhds hb] with z hz
  rw [frameMetric_det hz,Real.sqrt_sq (LinearMap.normDet_nonneg _)]

end FrameDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_TrueCenterLimit
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
section TrueCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance trueLimitFinite_r8a5371_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
attribute [local instance] OAI.WeakMTWTransport.trueLimitDualGroup
attribute [local instance] OAI.WeakMTWTransport.trueLimitDualSpace
local instance trueLimitBilinearGroup_r8a5371_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance trueLimitBilinearSpace_r8a5371_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma exists_true_center_limit_oai : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ),
    ∀J:(j:ℕ) → TrueCenterJet (n:=n) u a c (φ j) (lj j),
    ∀(l κ χ:ℝ) (q r:Model n) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    l∈U → 0<l → l<1 → 0<χ →
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
    Tendsto lj atTop (𝓝 l) →
    Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
    Tendsto (fun j=>(J j).q) atTop (𝓝 q) →
    Tendsto (fun j=>(J j).fullRay) atTop (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>(J j).curvature) atTop (𝓝 κ) →
    Tendsto (fun j=>(J j).matrix) atTop (𝓝 H) →
    (∀ᶠ j in atTop,χ≤expJacobian (J j).y (J j).p*
      (normalHessianOperator (J j).y (J j).p+(J j).A).det) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_true_center_jet_gain (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u a c φ lj J l κ χ q r H hlu hl hl1 hχ hq hlj hb hqq hfull hκ hH hvol
  let P:=fun j (V:Model n →L[ℝ] Model n →L[ℝ] ℝ)=>
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (bilinearOperator V).det=(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
        (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2*
        (normalHessianOperator (J j).y (J j).p+(J j).A).det ∧
      ∀d,V d d+δ*(1-lj j)*frameMetric a (J j).b d d+
        ((J j).curvature/(lj j)^2)*(frameMetric a (J j).b (J j).q d)^2≤(J j).matrix d d
  have hpos:∀ᶠ j in atTop,0<lj j ∧ lj j<1:=hlj.eventually (Ioo_mem_nhds hl hl1)
  have hVe:∀ᶠ j in atTop,∃V,P j V:=by
    filter_upwards [hpos,hlj.eventually (hU.mem_nhds hlu)] with j hj hju
    exact Hδ _ hju hj.1 hj.2 u a c (φ j) (J j)
  let V:=fun j=>if h:∃V,P j V then Classical.choose h else 0
  have hV:∀ᶠ j in atTop,P j (V j):=hVe.mono (fun j hj=>by
    simpa only [V,dite_eq_left hj] using Classical.choose_spec hj)
  let G:=fun j=>frameMetric a (J j).b
  let G₀:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a)
  have hb0:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hG:Tendsto G atTop (𝓝 G₀):=(frameMetric_continuousAt hb0).tendsto.comp hb
  have hf:=tendsto_clm_apply hG hqq
  have hshort:Tendsto (fun j=>(J j).shortRay) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=chartRay_tendsto hb hqq
  have hs:=continuous_expJacobian.continuousAt.tendsto.comp hshort
  have ha:=continuous_expJacobian.continuousAt.tendsto.comp hfull
  have hfr: Tendsto (fun j=>(chartFiberInverse a (J j).b).toLinearMap.normDet) atTop
      (𝓝 (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet):=
    (frameNormDet_continuousAt hb0).tendsto.comp hb
  let k:=fun j=>(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
    (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2*χ
  have hk:Tendsto k atTop (𝓝 ((chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
      (expJacobian a q)^2*χ)):=(((hfr.pow 2).mul (hlj.pow n)).mul (hs.pow 2)).mul_const χ
  have hk0:0<(chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
      (expJacobian a q)^2*χ:=by
    have Hf:=frameNormDet_pos hb0
    have He:=expJacobian_pos_of_injectivityDomain hq
    positivity
  have HVe:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧
      (∀d,V j d d+(δ*(1-lj j))*G j d d+
        ((J j).curvature/(lj j)^2)*(G j (J j).q d)^2≤(J j).matrix d d) ∧
      0≤expJacobian (J j).fullRay.1 (J j).fullRay.2 ∧
      k j≤expJacobian (J j).fullRay.1 (J j).fullRay.2*(bilinearOperator (V j)).det:=by
    filter_upwards [hV,hpos,hvol] with j hj hljj hvolj
    refine ⟨hj.1,?_,hj.2.2.2,expJacobian_nonneg _ _,?_⟩
    · intro d
      by_cases hd:d=0
      · simp [hd]
      · exact (hj.2.1 d hd).le
    · rw [hj.2.2.1]
      have hfactor:0≤(chartFiberInverse a (J j).b).toLinearMap.normDet^2*(lj j)^n*
          (expJacobian (J j).shortRay.1 (J j).shortRay.2)^2:=by
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hljj.1.le _)) (sq_nonneg _)
      have HH:=mul_le_mul_of_nonneg_left hvolj hfactor
      dsimp only [k,TrueCenterJet.fullRay]
      convert HH using 1 <;> first | rfl | ring
  have hbc:Tendsto (fun j=>δ*(1-lj j)) atTop (𝓝 (δ*(1-l))):=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hlj)
  have hcc:Tendsto (fun j=>(J j).curvature/(lj j)^2) atTop (𝓝 (κ/l^2)):=
    hκ.div (hlj.pow 2) (pow_ne_zero _ hl.ne')
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hgain,ha0,hdet⟩:=
    exists_bilinear_gain_limit hH hG hf ha hk hbc hcc hk0 HVe
  exact ⟨V₀,hVs,hVp,hgain,ha0,hdet⟩
end TrueCenterLimit
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_true_center_limit_oai.{u_1} := @OAI.WeakMTWTransport.exists_true_center_limit_oai.{u_1}
