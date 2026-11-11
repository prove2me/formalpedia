-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:20:22.143467+00:00
-- url     : https://prove2.me/submissions/90d42819-c59b-414c-adf8-b16ef622af5c

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
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_uniform_chart_outer_matrix
import Theorems.Thm_OAI_WeakMTWTransport_continuous_expJacobian

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma continuous_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.continuous.clm_apply continuous_const

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarSecond
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

lemma contDiff_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.clm_apply contDiff_const

lemma continuous_scalar_family_second {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>iteratedDeriv 2 (fun s=>Φ (p.1,s)) p.2) := by
  have H:=continuous_scalar_family_deriv (contDiff_scalar_family_deriv hΦ)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H

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

lemma bilinear_quadratic_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ} {ε:ℝ} (h : ‖A-B‖≤ε) (d:E) :
    A d d≤B d d+ε*‖d‖^2 := by
  have H := (le_abs_self ((A-B) d d)).trans (bilinear_quadratic_norm_bound (A-B) d)
  have HH := H.trans (mul_le_mul_of_nonneg_right h (sq_nonneg ‖d‖))
  simpa only [_root_.sub_apply,sub_le_iff_le_add,add_comm] using HH

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

lemma bilinearMatrix_nonneg {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d) :
    (bilinearMatrix B).PosSemidef := by
  apply (LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℝ E)).2
  exact (LinearMap.isPositive_iff _).2 ⟨bilinearOperator_symmetric hs,by
    intro d
    change 0 ≤ inner ℝ (bilinearOperator B d) d
    rw [bilinearOperator_inner]
    exact hp d⟩

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
local instance gainBilinearGroup_r4fa649_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gainBilinearSpace_r4fa649_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma rankForm_tendsto {f:ℕ → E →L[ℝ] ℝ} {g:E →L[ℝ] ℝ}
    (hf:Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j=>(f j).smulRight (f j)) atTop (𝓝 (g.smulRight g)) :=
  (isBoundedBilinearMap_smulRight.continuous.continuousAt.tendsto).comp (hf.prodMk_nhds hf)

end BilinearGainLimit
end WeakMTWTransport

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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RankOneCoercive
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
section RankOneCoercive
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma positive_bilinear_uniform_lower [FiniteDimensional ℝ E]
    {B:E →L[ℝ] E →L[ℝ] ℝ} (hB:∀d,d≠0 → 0 < B d d) :
    ∃c>0,∀d:E,c*‖d‖^2 ≤ B d d := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    refine ⟨1,zero_lt_one,?_⟩
    intro d
    have :d=0:=Subsingleton.elim _ _
    simp [this]
  | inr h =>
    let := h
    have hs:(Metric.sphere (0:E) 1).Nonempty:=NormedSpace.sphere_nonempty.mpr (by norm_num)
    have hc:Continuous (fun d:E=>B d d):=B.continuous.clm_apply continuous_id
    obtain ⟨v,hv,hmin⟩:=(isCompact_sphere (0:E) 1).exists_isMinOn hs hc.continuousOn
    have hvn:‖v‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using hv
    have hv0:v≠0:=by intro H; simp [H] at hvn
    refine ⟨B v v,hB v hv0,?_⟩
    intro d
    by_cases hd:d=0
    · simp [hd]
    have hn:0 < ‖d‖:=norm_pos_iff.mpr hd
    have hdmem:‖d‖⁻¹ • d∈Metric.sphere (0:E) 1:=by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
    have H:B v v ≤ B (‖d‖⁻¹ • d) (‖d‖⁻¹ • d):=hmin hdmem
    simp only [map_smul,_root_.smul_apply,smul_eq_mul] at H
    have H':B v v*‖d‖^2 ≤ (‖d‖⁻¹*(‖d‖⁻¹*B d d))*‖d‖^2:=
      mul_le_mul_of_nonneg_right H (sq_nonneg _)
    convert H' using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end RankOneCoercive
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveDetCompact
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
section PositiveDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.WeakMTWTransport.positiveCompactDualGroup
attribute [local instance] OAI.WeakMTWTransport.positiveCompactDualSpace
local instance positiveCompactBilinearGroup_r4fa649_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance positiveCompactBilinearSpace_r4fa649_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma bilinear_eventual_coercivity
    {B:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (hpos:∀d,d≠0 → 0 < B₀ d d) :
    ∃m>0,∀ᶠ k in atTop,∀d:E,m*‖d‖^2 ≤ B k d d := by
  obtain ⟨c,hc,HC⟩:=positive_bilinear_uniform_lower hpos
  have hn:Tendsto (fun k=>‖B₀-B k‖) atTop (𝓝 0):=by
    simpa only [sub_self,norm_zero] using (show Tendsto (fun k=>B₀-B k) atTop (𝓝 (B₀-B₀)) from tendsto_const_nhds.sub hB).norm
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hn.eventually (gt_mem_nhds (half_pos hc))] with k hk
  intro d
  have H:=bilinear_quadratic_close hk.le d
  nlinarith only [H,HC d]

lemma exists_bilinear_limit_of_det_lower
    {B V:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (hpos:∀d,d≠0 → 0 < B₀ d d)
    (hV:∀ᶠ k in atTop,(∀d e,V k d e=V k e d) ∧ ∀d,B k d d ≤ V k d d)
    {K:ℝ} (hK:0 ≤ K) (hdet:∀ᶠ k in atTop,|(bilinearOperator (V k)).det| ≤ K) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧
      (∀d e,V₀ d e=V₀ e d) ∧ (∀d,B₀ d d ≤ V₀ d d) ∧
      (∀d,d≠0 → 0 < V₀ d d) := by
  obtain ⟨m,hm,Hm⟩:=bilinear_eventual_coercivity hB hpos
  let C:ℝ:=(Module.finrank ℝ E:ℝ)*K/m^(Module.finrank ℝ E-1)
  have hC:0 ≤ C:=by dsimp only [C] <;> positivity
  have Hbound:∀ᶠ k in atTop,‖V k‖ ≤ C:=by
    filter_upwards [Hm,hV,hdet] with k hk hv hd
    have hlo:∀d:E,m*‖d‖^2 ≤ V k d d:=fun d=>(hk d).trans (hv.2 d)
    apply symmetric_bilinear_norm_bound hv.1 hC
    intro d
    rw [abs_of_nonneg ((mul_nonneg hm.le (sq_nonneg _)).trans (hlo d))]
    exact bilinear_quadratic_bound_of_det hm hlo hd d
  obtain ⟨V₀,σ,hσ,HV⟩:=exists_bilinear_limit Hbound
  have Hlower:∀d,B₀ d d ≤ V₀ d d:=by
    intro d
    exact le_of_tendsto_of_tendsto
      (tendsto_clm_apply (tendsto_clm_apply (hB.comp hσ.tendsto_atTop) tendsto_const_nhds) tendsto_const_nhds)
      (tendsto_clm_apply (tendsto_clm_apply HV tendsto_const_nhds) tendsto_const_nhds)
      (hσ.tendsto_atTop.eventually (hV.mono (fun k hk=>hk.2 d)))
  refine ⟨V₀,σ,hσ,HV,?_,Hlower,fun d hd=>(hpos d hd).trans_le (Hlower d)⟩
  exact bilinear_limit_symm HV (hσ.tendsto_atTop.eventually (hV.mono (fun k hk=>hk.1)))

end PositiveDetCompact
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OuterDetCompact
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
section OuterDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_outer_matrix_limit {V B:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {B₀:E →L[ℝ] E →L[ℝ] ℝ} {a k:ℕ → ℝ} {a₀ k₀:ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (ha:Tendsto a atTop (𝓝 a₀))
    (hk:Tendsto k atTop (𝓝 k₀)) (ha0:0 < a₀)
    (hpos:∀d,d≠0 → 0 < B₀ d d)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,B j d d ≤ V j d d) ∧
      a j*(bilinearOperator (V j)).det ≤ k j) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0 < V₀ d d) ∧ (∀d,B₀ d d ≤ V₀ d d) ∧
      a₀*(bilinearOperator V₀).det ≤ k₀ := by
  let K:=2*(|k₀|+1)/a₀
  have hK:0 ≤ K:=by dsimp only [K] <;> positivity
  have hbound:∀ᶠ j in atTop,|(bilinearOperator (V j)).det| ≤ K:=by
    filter_upwards [hV,ha.eventually (lt_mem_nhds (show a₀/2<a₀ by linarith)),
      hk.eventually (gt_mem_nhds (show k₀ < |k₀|+1 from lt_of_le_of_lt (le_abs_self k₀) (by linarith)))]
      with j hj haj hkj
    have hd:=bilinear_det_nonneg hj.1 hj.2.1
    rw [abs_of_nonneg hd]
    have H:(a₀/2)*(bilinearOperator (V j)).det≤|k₀|+1:=
      (mul_le_mul_of_nonneg_right haj.le hd).trans (hj.2.2.2.trans hkj.le)
    dsimp only [K]
    apply (le_div_iff₀ ha0).mpr
    nlinarith only [H]
  obtain ⟨V₀,σ,hσ,HV,hVs,hlo,hp⟩:=exists_bilinear_limit_of_det_lower hB hpos
    (hV.mono (fun j hj=>⟨hj.1,hj.2.2.1⟩)) hK hbound
  refine ⟨V₀,σ,hσ,HV,hVs,hp,hlo,?_⟩
  exact le_of_tendsto_of_tendsto
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV)) (hk.comp hσ.tendsto_atTop)
    ((hσ.tendsto_atTop.eventually hV).mono (fun j hj=>hj.2.2.2))
end OuterDetCompact
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OriginalOuterLimit
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
section OriginalOuterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance originalOuterFinite_r4fa649_1 (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance originalOuterComplete_r4fa649_1 (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _
attribute [local instance] OAI.WeakMTWTransport.originalOuterDualGroup
attribute [local instance] OAI.WeakMTWTransport.originalOuterDualSpace
local instance originalOuterBilinearGroup_r4fa649_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance originalOuterBilinearSpace_r4fa649_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.exists_original_outer_limit_oai
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) :
    ∃K>0,∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (Φ:ℝ×ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → ContDiff ℝ ∞ Φ →
      ∀(a:M) (bj pj:ℕ → Model n) (γj mj:ℕ → ℝ)
        (Lj:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ)
        (γ m l κ:ℝ) (p:Model n) (L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
      (show TangentSpace 𝓘(ℝ,Model n) a from p)∈minimizingVectors a →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) → Tendsto pj atTop (𝓝 p) →
      Tendsto γj atTop (𝓝 γ) → Tendsto mj atTop (𝓝 m) → Tendsto Lj atTop (𝓝 L) →
      deriv (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=l →
      iteratedDeriv 2 (fun s=>Φ (γ,s)) (uv.2 (riemannianExp a p))=κ →
      1 < l → κ < 0 →
      (∀d,d≠0 → 0 < m*L d d-(κ/l^2)*
        (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2) →
      (∀ᶠ j in atTop,bj j∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
        StrictMono (fun s=>Φ (γj j,s)) ∧
        (chartRay a (bj j) (pj j)).2∈activeLogs ((fun s=>Φ (γj j,s)) ∘ uv.2)
          (chartRay a (bj j) (pj j)).1 ∧
        0 ≤ mj j ∧ (∀d e,Lj j d e=Lj j e d) ∧ (∀d,0 ≤ Lj j d d) ∧
        HasLowerSecondTaylor (fun d=>Φ (γj j,uv.2 (movingNormal a (bj j,pj j+d)))+
          ‖chartFiberInverse a (bj j) (pj j+d)‖^2/2) 0 (mj j • Lj j)) →
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
        (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0 < V d d) ∧
        (∀d,m*L d d-(κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) p d)^2 ≤ V d d) ∧
        expJacobian (n:=n) (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1
          (l⁻¹ • (reverseRay (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).2)*(bilinearOperator V).det ≤
          (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*
            (expJacobian (n:=n) a p)^2 := by
  classical
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_chart_outer_matrix hlam hcap
  refine ⟨K,hK,?_⟩
  intro x0 uv Φ huv hΦ a bj pj γj mj Lj γ m l κ p L hmin hb hp hγ hm hL hd hdd hl hκneg hpos hgood
  let z:=fun j=>chartRay a (bj j) (pj j)
  let z₀:TangentBundle 𝓘(ℝ,Model n) M:=⟨a,p⟩
  let sj:=fun j=>uv.2 (riemannianExp (z j).1 (z j).2)
  let lj:=fun j=>deriv (fun s=>Φ (γj j,s)) (sj j)
  let κj:=fun j=>iteratedDeriv 2 (fun s=>Φ (γj j,s)) (sj j)
  have hz:Tendsto z atTop (𝓝 z₀):=chartRay_tendsto hb hp
  have he:Tendsto (fun j=>riemannianExp (z j).1 (z j).2) atTop (𝓝 (riemannianExp a p)):=
    (contMDiff_riemannianExp (n:=n) (M:=M)).continuous.continuousAt.tendsto.comp hz
  have hs:Tendsto sj atTop (𝓝 (uv.2 (riemannianExp a p))):=uv.2.continuous.continuousAt.tendsto.comp he
  have hlj:Tendsto lj atTop (𝓝 l):=by
    rw [←hd]
    exact ((continuous_scalar_family_deriv hΦ).tendsto (γ,uv.2 (riemannianExp a p))).comp (hγ.prodMk_nhds hs)
  have hκj:Tendsto κj atTop (𝓝 κ):=by
    rw [←hdd]
    have H:=((continuous_scalar_family_second hΦ).tendsto (γ,uv.2 (riemannianExp a p))).comp (hγ.prodMk_nhds hs)
    exact H
  have hl0:0 < l:=zero_lt_one.trans hl
  have hcur:∀ᶠ j in atTop,1 < lj j ∧ κj j < 0:=
    (hlj.eventually (lt_mem_nhds hl)).and (hκj.eventually (gt_mem_nhds hκneg))
  let P:=fun j (V:Model n →L[ℝ] Model n)=>
    (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧ (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
    (∀d,mj j*Lj j d d-(κj j/(lj j)^2)*(frameMetric a (bj j) (pj j) d)^2 ≤ inner ℝ (V d) d) ∧
    expJacobian (n:=n) (reverseRay (z j)).1 ((lj j)⁻¹ • (reverseRay (z j)).2)*V.det ≤
      (chartFiberInverse a (bj j)).toLinearMap.normDet^2*(lj j)^n*K*(expJacobian (n:=n) (z j).1 (z j).2)^2
  have hVe:∀ᶠ j in atTop,∃V,P j V:=by
    filter_upwards [hgood,hcur] with j hj hc
    have hf:ContDiff ℝ ∞ (fun s=>Φ (γj j,s)):=hΦ.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨V,hVs,hVp,hgain,_,_,hdet⟩:=HK x0 uv (fun s=>Φ (γj j,s)) huv hf.continuous
      hj.2.1 a (bj j) (pj j) hj.1 (lj j) hj.2.2.1
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
      (hf.differentiable (by norm_num) (sj j)).hasDerivAt hc.1 hc.2.le
      (mj j • Lj j) (fun d e=>by simp only [smul_apply,smul_eq_mul,hj.2.2.2.2.1])
      (fun d=>mul_nonneg hj.2.2.2.1 (hj.2.2.2.2.2.1 d)) hj.2.2.2.2.2.2
    exact ⟨V,hVs,hVp,hgain,hdet⟩
  let Vj:=fun j=>if h:∃V,P j V then Classical.choose h else 0
  have hVj:∀ᶠ j in atTop,P j (Vj j):=hVe.mono (fun j hj=>by
    simpa only [Vj,dite_eq_left hj] using Classical.choose_spec hj)
  let W:=fun j=>(innerSL ℝ).comp (Vj j)
  let G:=fun j=>frameMetric a (bj j)
  let G₀:=frameMetric a (extChartAt 𝓘(ℝ,Model n) a a)
  have hb0:=mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a
  have hG:Tendsto G atTop (𝓝 G₀):=(frameMetric_continuousAt hb0).tendsto.comp hb
  have hfc:=tendsto_clm_apply hG hp
  have hc:Tendsto (fun j=>κj j/(lj j)^2) atTop (𝓝 (κ/l^2)):=hκj.div (hlj.pow 2) (pow_ne_zero _ hl0.ne')
  let Bj:=fun j=>mj j • Lj j-(κj j/(lj j)^2) • (G j (pj j)).smulRight (G j (pj j))
  let B₀:=m • L-(κ/l^2) • (G₀ p).smulRight (G₀ p)
  have hB:Tendsto Bj atTop (𝓝 B₀):=(hm.smul hL).sub (hc.smul (rankForm_tendsto hfc))
  have hBpos:∀d,d≠0 → 0 < B₀ d d:=by
    intro d hd
    simpa only [B₀,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc] using hpos d hd
  let aj:=fun j=>expJacobian (n:=n) (reverseRay (z j)).1 ((lj j)⁻¹ • (reverseRay (z j)).2)
  let a₀:=expJacobian (n:=n) (reverseRay z₀).1 (l⁻¹ • (reverseRay z₀).2)
  have hreverse:=continuous_reverseRay.continuousAt.tendsto.comp hz
  have ha:Tendsto aj atTop (𝓝 a₀):=continuous_expJacobian.continuousAt.tendsto.comp
    (contMDiff_tangentScale.continuous.continuousAt.tendsto.comp ((hlj.inv₀ hl0.ne').prodMk_nhds hreverse))
  have ha0:0 < a₀:=expJacobian_pos_of_injectivityDomain
    (contracted_minimizer_mem_injectivityDomain (reverseRay_minimizing hmin)
      (inv_pos.mpr hl0) (inv_lt_one_of_one_lt₀ hl))
  have hσ:=continuous_expJacobian.continuousAt.tendsto.comp hz
  have hfr: Tendsto (fun j=>(chartFiberInverse a (bj j)).toLinearMap.normDet) atTop
      (𝓝 (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet):=
    (frameNormDet_continuousAt hb0).tendsto.comp hb
  let kj:=fun j=>(chartFiberInverse a (bj j)).toLinearMap.normDet^2*(lj j)^n*K*(expJacobian (z j).1 (z j).2)^2
  have hk:Tendsto kj atTop (𝓝 ((chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*K*(expJacobian a p)^2)):=
    (((hfr.pow 2).mul (hlj.pow n)).mul_const K).mul (hσ.pow 2)
  have HW:∀ᶠ j in atTop,(∀d e,W j d e=W j e d) ∧ (∀d,0 ≤ W j d d) ∧
      (∀d,Bj j d d≤W j d d) ∧ aj j*(bilinearOperator (W j)).det≤kj j:=by
    filter_upwards [hVj] with j hj
    have hw (d e:Model n):W j d e=inner ℝ (Vj j d) e:=rfl
    refine ⟨?_,?_,?_,?_⟩
    · intro d e
      rw [hw,hw,hj.1,real_inner_comm]
    · intro d
      rw [hw]
      by_cases hd:d=0
      · simp [hd]
      · exact (hj.2.1 d hd).le
    · intro d
      simpa only [Bj,sub_apply,smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc,hw] using hj.2.2.1 d
    · have hW:bilinearOperator (W j)=Vj j:=by
        apply ContinuousLinearMap.ext
        intro d
        apply ext_inner_right ℝ
        intro e
        exact bilinearOperator_inner _ _ _
      rw [hW]
      exact hj.2.2.2
  obtain ⟨V,σ,hσ,HV,hVs,hVp,hgain,hdet⟩:=exists_outer_matrix_limit hB ha hk ha0 hBpos HW
  refine ⟨V,hVs,hVp,?_,hdet⟩
  intro d
  simpa only [B₀,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two,mul_assoc] using hgain d
end OriginalOuterLimit
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit_oai.{u_1}
