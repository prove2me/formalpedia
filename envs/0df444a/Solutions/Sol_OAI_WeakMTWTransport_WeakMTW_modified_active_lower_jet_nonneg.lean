-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:22.257754+00:00
-- url     : https://prove2.me/submissions/672a4d6a-674a-4ad0-964e-bfce3a86900c

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
import Definitions.Def_OAIQ232A031
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_kernel
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_residual_taylor
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_taylor
import Theorems.Thm_OAI_WeakMTWTransport_prefixDefect_taylor

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FullSet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

lemma HasSecondTaylor.eventually {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h in 𝓝 (0:E), |f h-f 0-l h-B h h/2|≤ε*‖h‖^2 := by
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hf.def hε

lemma hasSecondTaylor_of_contDiffAt {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    HasSecondTaylor f (fderiv ℝ f 0) (fderiv ℝ (fderiv ℝ f) 0) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hn := hf.eventually (by norm_num)
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuousAt
  have he : ∀ᶠ z : E in 𝓝 0,
      ‖fderiv ℝ (fderiv ℝ f) z-fderiv ℝ (fderiv ℝ f) 0‖<ε := by
    exact Metric.tendsto_nhds.mp hD ε hε |>.mono (fun _ h => by simpa only [dist_eq_norm] using h)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hn.and he)
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  have H := second_order_remainder_bound_on_ball hr hε.le
    (fun z hz => (hball hz).1) (fun z hz => (hball hz).2.le) hh
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using H

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

lemma HasSecondTaylor.comp_stationary {f : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasSecondTaylor f 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0) :
    HasSecondTaylor (fun h => f (a h)) 0
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)) := by
  have hO : (fun h : E => ‖a h‖) =O[𝓝 0] (fun h => ‖h‖) := by
    simpa only [ha0,sub_zero] using ha.isBigO_sub.norm_left.norm_right
  have ht : Tendsto a (𝓝 0) (𝓝 0) := ha0 ▸ ha.continuousAt
  have h1 := (hf.comp_tendsto ht).trans_isBigO (hO.pow 2)
  have h2 : (fun h => (B (a h) (a h)-B (A h) (A h))/2) =o[𝓝 0]
      (fun h : E => ‖h‖^2) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (bilinear_remainder_of_hasFDerivAt ha ha0 B).const_mul_left (2:ℝ)⁻¹
  unfold HasSecondTaylor
  have he : (fun h => f (a h)-f (a 0)-(0 : E →L[ℝ] ℝ) h-
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (B.comp A)) h h/2) =
      (fun h => (f (a h)-f 0-(0 : F →L[ℝ] ℝ) (a h)-B (a h) (a h)/2)+
        (B (a h) (a h)-B (A h) (A h))/2) := by
    funext h
    simp only [ha0,_root_.zero_apply,sub_zero,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
    ring
  rw [he]
  exact h1.add h2

lemma HasSecondTaylor.sub {f g : E → ℝ} {l k : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B)
    (hg : HasSecondTaylor g k C) : HasSecondTaylor (fun h => f h-g h) (l-k) (B-C) := by
  unfold HasSecondTaylor at *
  have he : (fun h => (f h-g h)-(f 0-g 0)-(l-k) h-(B-C) h h/2) =
      (fun h => (f h-f 0-l h-B h h/2)-(g h-g 0-k h-C h h/2)) := by
    funext h
    simp only [_root_.sub_apply]
    ring
  rw [he]
  exact Asymptotics.IsLittleO.sub hf hg

lemma HasSecondTaylor.add {f g : E → ℝ} {l k : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B)
    (hg : HasSecondTaylor g k C) : HasSecondTaylor (fun h => f h+g h) (l+k) (B+C) := by
  unfold HasSecondTaylor at *
  have he : (fun h => (f h+g h)-(f 0+g 0)-(l+k) h-(B+C) h h/2) =
      (fun h => (f h-f 0-l h-B h h/2)+(g h-g 0-k h-C h h/2)) := by
    funext h
    simp only [_root_.add_apply]
    ring
  rw [he]
  exact Asymptotics.IsLittleO.add hf hg

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LowerTaylor
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HasSecondTaylor.comp_linear {f : F → ℝ} {l : F →L[ℝ] ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (A : E →L[ℝ] F) :
    HasSecondTaylor (fun h => f (A h)) (l.comp A) (pullBilinear B A) := by
  have H := (hf.comp_tendsto (show Tendsto A (𝓝 0) (𝓝 0) by
    simpa only [ContinuousAt,map_zero] using (A.continuous.continuousAt (x := (0:E))))).trans_isBigO
      ((A.isBigO_id (𝓝 0)).norm_left.norm_right.pow 2)
  simpa only [HasSecondTaylor,map_zero,Function.comp_def,ContinuousLinearMap.comp_apply,
    pullBilinear_apply] using H

lemma HasSecondTaylor.sub_linear {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) :
    HasSecondTaylor (fun h => f h-l h) 0 B := by
  unfold HasSecondTaylor at *
  have heq : (fun h => f h-l h-(f 0-l 0)-(0 : E →L[ℝ] ℝ) h-B h h/2) =
      (fun h => f h-f 0-l h-B h h/2) := by
    funext h; simp only [map_zero,sub_zero,zero_apply] <;> ring
  rw [heq]; exact hf

lemma HasLowerSecondTaylor.mono {f g : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (he : f 0=g 0) (hle : f≤ᶠ[𝓝 0] g) : HasLowerSecondTaylor g l B := by
  intro ε hε
  filter_upwards [hf ε hε,hle] with h hh hfg
  rw [←he]
  exact hh.trans hfg

lemma HasLowerSecondTaylor.of_positive_mul {f : E → ℝ} {m : ℝ} (hm : 0 < m)
    {l : E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasLowerSecondTaylor (fun h => m * f h) l B) :
    HasLowerSecondTaylor f (m⁻¹ • l) (m⁻¹ • B) := by
  intro ε hε
  filter_upwards [hf (m*ε) (mul_pos hm hε)] with h hh
  apply (mul_le_mul_iff_right₀ hm).mp
  simpa only [smul_apply,smul_eq_mul,mul_sub,mul_add,
    mul_div_assoc,←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul] using hh

lemma lowerTaylor_of_stationary_transfer {S : F → ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} (hS : HasSecondTaylor S 0 B)
    {a : E → F} {A : E →L[ℝ] F} (ha : HasFDerivAt a A 0) (ha0 : a 0=0)
    {f : E → ℝ} {l : E →L[ℝ] ℝ} {C : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : HasSecondTaylor f l C)
    {ψ : E → ℝ} {m : ℝ} (hm : 0 < m)
    (hle : ∀ᶠ h in 𝓝 (0:E),
      S (a h)-S 0-(f h-f 0-l h)≤ m * (ψ h-ψ 0)) :
    HasLowerSecondTaylor ψ 0 (m⁻¹ • (pullBilinear B A-C)) := by
  have hcomp := (hS.comp_stationary ha ha0).sub hf.sub_linear
  have hE : ∀ h:E, (S (a h)-(f h-l h))-(S (a 0)-(f 0-l 0)) =
      S (a h)-S 0-(f h-f 0-l h) := by
    intro h; rw [ha0,map_zero]; ring
  have hlow : HasLowerSecondTaylor (fun h => m * ψ h) 0 (pullBilinear B A-C) := by
    intro ε hε
    filter_upwards [hcomp.eventually hε,hle] with h hh hbound
    have hh' : |(S (a h)-(f h-l h))-(S (a 0)-(f 0-l 0))-
        (pullBilinear B A-C) h h/2|≤ε*‖h‖^2 := by
      simpa only [zero_sub,sub_zero,zero_apply,pullBilinear] using hh
    rw [hE] at hh'
    simp only [zero_apply,add_zero]
    have H := (abs_le.mp hh').1
    nlinarith
  simpa only [smul_zero] using hlow.of_positive_mul hm

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

lemma hasSecondTaylor_shift {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasSecondTaylor (fun h => f (x+h)) (fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) x) := by
  have hc : ContDiffAt ℝ 2 (fun h => f (x+h)) 0 := by
    exact (show ContDiffAt ℝ 2 f (x+(0:E)) by simpa using hf).comp 0
      (contDiffAt_const.add contDiffAt_id)
  have H := hasSecondTaylor_of_contDiffAt hc
  have hD : fderiv ℝ (fun h => f (x+h)) 0=fderiv ℝ f x := by
    have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt
    have hl := (hasFDerivAt_id (𝕜 := ℝ) (0:E)).const_add x
    simpa only [add_zero,ContinuousLinearMap.comp_id,Function.comp_def] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:E)) by simpa using hd).comp
        (f := fun h : E => x+h) 0 hl).fderiv
  have hDD : fderiv ℝ (fderiv ℝ (fun h => f (x+h))) 0=
      fderiv ℝ (fderiv ℝ f) x := by
    ext v w
    simpa only [ContinuousLinearMap.id_apply,add_zero] using
      second_fderiv_comp_affine (ContinuousLinearMap.id ℝ E) x 0
        (by simpa using hf) v w
  rwa [hD,hDD] at H

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

lemma norm_square_hasSecondTaylor (p : E) :
    HasSecondTaylor (fun h : E => ‖p+h‖^2/2) (innerSL ℝ p) (innerSL ℝ) := by
  have hc : ContDiffAt ℝ 2 (fun v : E => ‖v‖^2/2) p :=
    ((half_norm_sq_contDiff (E := E)).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := hasSecondTaylor_shift hc
  simpa only [half_norm_sq_fderiv,(innerSL ℝ).hasFDerivAt.fderiv] using H

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SplitEndpointCost
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

lemma splitEndpointCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (splitEndpointCost x s) (0,p) := by
  exact (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x =>
      (q.2,(q.1,q.2))) (0,p)
    (contDiffAt_snd.prodMk (contDiffAt_fst.prodMk contDiffAt_snd))

lemma splitEndpointCost_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    splitEndpointCost x s (0,p)=‖p‖^2/2 := by
  have hm := injectivityDomain_subset_minimizingVectors x hleft
  have hn := injectivityDomain_subset_minimizingVectors _ hright
  change dist x (riemannianExp x (s • p))=‖s • p‖ at hm
  change dist (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (riemannianExp _ ((1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) = _ at hn
  rw [shifted_exp_endpoint] at hn
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hm
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs1),sprayFlow_speed] at hn
  simp only [splitEndpointCost,splitNormalAction,riemannianExp_zero,cost]
  rw [hm,riemannianExp_smul,hn]
  field_simp
  ring

lemma splitEndpointCost_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    (fun v => splitEndpointCost x s (0,v)) =ᶠ[𝓝 p] (fun v => ‖v‖^2/2) := by
  filter_upwards [split_regular_legs_near hleft hright] with v hv
  exact splitEndpointCost_axis hs hs1 hv.1 hv.2

lemma splitEndpointCost_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : s ≠ 0) (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) = -inner ℝ p a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hB := (splitNormalAction_contDiffAt hleft hright).comp (0,p)
    (contDiffAt_const.prodMk contDiffAt_id)
  have hL : HasFDerivAt (fun b : V => (b,p))
      ((ContinuousLinearMap.id ℝ V).prod 0) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk (hasFDerivAt_const p (0:V))
  have hc := hC.hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have hb := (hB.differentiableAt (by simp)).hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have he := congrArg (fun A : V →L[ℝ] ℝ => A a) (hc.unique hb)
  change fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) =
    fderiv ℝ (splitNormalAction x s p) (0,p) (a,0) at he
  rw [he]
  exact splitNormalAction_source_gradient hs hleft (hB.differentiableAt (by simp)) a

lemma splitEndpointCost_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : s ≠ 0) (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (0,d) (a,0) =
      -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (splitEndpointCost x s) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    filter_upwards [split_regular_legs_near hleft hright] with v hv
    exact splitEndpointCost_source_gradient hs hv.1 hv.2 a
  have hi : HasFDerivAt (fun v : V => -inner ℝ v a) (-(innerSL ℝ a)) p := by
    convert! ((innerSL ℝ a).hasFDerivAt (x := p)).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext v; exact congrArg Neg.neg (real_inner_comm a v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq heq.symm).unique hi)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,map_zero,add_zero,zero_add,add_apply,
    ContinuousLinearMap.comp_zero,Function.comp_apply,
    ContinuousLinearMap.flip_apply,neg_apply,innerSL_apply_apply,real_inner_comm] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SplitEndpointJets
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

lemma splitEndpointCost_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,0) (a,0) =
      hessianValue x (s • p) a / s := by
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := iteratedDeriv_two_affine_line hC (a,0)
  rw [← H]
  have he : (fun r : ℝ => splitEndpointCost x s ((0,p)+r • (a,0))) =
      (fun r => cost (riemannianExp x (s • p)) (riemannianExp x p)/(1-s) +
        cost (riemannianExp x (r • a)) (riemannianExp x (s • p))/s) := by
    funext r
    simp only [splitEndpointCost, splitNormalAction, Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_zero,zero_add,add_zero]
    exact add_comm _ _
  rw [he,iteratedDeriv_const_add (by norm_num : 0<2),iteratedDeriv_div_const]
  rfl

lemma splitEndpointCost_endpoint_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitEndpointCost x s) (0,p) (0,d) = inner ℝ p d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (hC.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).congr_of_eventuallyEq
    (splitEndpointCost_axis_near hs hs1 hleft hright).symm
  have he := congrArg (fun A : V →L[ℝ] ℝ => A d) (hd.unique (half_norm_sq_hasFDerivAt p))
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply] using he

lemma splitEndpointCost_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (0,d) (0,e) = inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let L : V →L[ℝ] V×V := (0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq := ((splitEndpointCost_axis_near hs hs1 hleft hright).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have he := congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ => A d e) heq
  have H := second_fderiv_comp_affine L (0:V×V) p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [← H,he,half_norm_sq_second_fderiv]

lemma splitEndpointCost_hessian_diag {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,d) (a,d) =
      hessianValue x (s • p) a / s - 2*inner ℝ a d + ‖d‖^2 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hsplit : (a,d)=((a,0):V×V)+(0,d) := by simp
  have hsym := (splitEndpointCost_contDiffAt hleft hright).isSymmSndFDerivAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [hsplit]
  simp only [map_add,add_apply]
  rw [splitEndpointCost_source_hessian hleft hright,
    hsym.eq (a,0) (0,d),
    splitEndpointCost_mixed hs.ne' hleft hright,
    splitEndpointCost_endpoint_hessian hs hs1 hleft hright]
  rw [real_inner_self_eq_norm_sq,real_inner_comm d a]
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FiniteTaylor
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
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.const_mul' {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul] <;> ring
  rw [he]
  exact hf.const_mul_left c

lemma HasSecondTaylor.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    {l : ι → E →L[ℝ] ℝ} {B : ι → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ i∈s, HasSecondTaylor (f i) (l i) (B i)) :
    HasSecondTaylor (fun h => ∑ i∈s, f i h) (∑ i∈s, l i) (∑ i∈s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp only [HasSecondTaylor,sub_self,zero_apply,zero_div]
    exact Asymptotics.isLittleO_zero _ _
  | @insert i s hi IH =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasLowerSecondTaylor.mono_diagonal {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (hBC : ∀ h:E, C h h≤B h h) : HasLowerSecondTaylor f l C := by
  intro ε hε
  filter_upwards [hf ε hε] with h hh
  have H := hBC h
  linarith

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitDefect_taylor {x : M} {s : ℝ} (hs : 0 < s) (hs1 : s<1)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : s • p∈injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
      HasSecondTaylor (splitDefect x s p)
        ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
      ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
        B (a,d) (a,d)=hessianValue x (s • p) a/s-2*inner ℝ a d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let P : V×V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  let H := fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p)
  let D := H-pullBilinear (innerSL ℝ) P
  have hC := (splitEndpointCost_contDiffAt hp hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HT := (hasSecondTaylor_shift hC).sub
    ((norm_square_hasSecondTaylor p).comp_linear P)
  have hlin : fderiv ℝ (splitEndpointCost x s) (0,p)-((innerSL ℝ p).comp P)=
      (-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ V V) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    change fderiv ℝ (splitEndpointCost x s) (0,p) (a,d)-inner ℝ p d = -inner ℝ p a
    rw [show (a,d)=((a,0):V×V)+(0,d) by simp,map_add,
      splitEndpointCost_source_gradient hs.ne' hp hright,
      splitEndpointCost_endpoint_gradient hs hs1 hp hright]
    ring
  rw [hlin] at HT
  refine ⟨D,?_,?_⟩
  · convert! HT using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    rcases h with ⟨a,d⟩
    simp only [splitDefect,Prod.mk_add_mk,zero_add,P,ContinuousLinearMap.coe_snd']
  · intro a d
    change fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,d) (a,d)-inner ℝ d d=_
    rw [splitEndpointCost_hessian_diag hs hs1 hp hright,real_inner_self_eq_norm_sq]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_WeightedDefect
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_defect_taylor (w : ι → ℝ) (p : ι → E) (i : ι)
    {b : E×E → ℝ} {c : ι → E×E → ℝ}
    {B : E×E →L[ℝ] E×E →L[ℝ] ℝ}
    {C : ι → E×E →L[ℝ] E×E →L[ℝ] ℝ}
    {q : E → ℝ} {r : ι → E → ℝ}
    (hb : HasSecondTaylor b ((-innerSL ℝ (∑ j,w j • p j)).comp
      (ContinuousLinearMap.fst ℝ E E)) B)
    (hc : ∀ j, HasSecondTaylor (c j) ((-innerSL ℝ (p j)).comp
      (ContinuousLinearMap.fst ℝ E E)) (C j))
    (hB : ∀ a d:E, B (a,d) (a,d)=q a-2*inner ℝ a d)
    (hC : ∀ j (a d:E), C j (a,d) (a,d)=r j a-2*inner ℝ a d) :
    ∃ D : E×E →L[ℝ] E×E →L[ℝ] ℝ,
      HasSecondTaylor (fun h:E×E => b (h.1,w i • h.2)-
        ∑ j,w j*c j (h.1,if j=i then h.2 else 0)) 0 D ∧
      ∀ a d:E, D (a,d) (a,d)=q a-∑ j,w j*r j a := by
  let J : E×E →L[ℝ] E×E := (ContinuousLinearMap.fst ℝ E E).prod
    (w i • ContinuousLinearMap.snd ℝ E E)
  let K : ι → E×E →L[ℝ] E×E := fun j => (ContinuousLinearMap.fst ℝ E E).prod
    (if j=i then ContinuousLinearMap.snd ℝ E E else 0)
  have HTc : ∀ j, HasSecondTaylor (fun h => w j * c j (K j h))
      (w j • (((-innerSL ℝ (p j)).comp (ContinuousLinearMap.fst ℝ E E)).comp (K j)))
      (w j • pullBilinear (C j) (K j)) := fun j =>
        ((hc j).comp_linear (K j)).const_mul' (w j)
  have HCsum := HasSecondTaylor.sum (f := fun j h => w j*c j (K j h))
    (l := fun j => w j • (((-innerSL ℝ (p j)).comp (ContinuousLinearMap.fst ℝ E E)).comp (K j)))
    (B := fun j => w j • pullBilinear (C j) (K j)) Finset.univ (fun j _ => HTc j)
  have HT := (hb.comp_linear J).sub HCsum
  have hl : (((-innerSL ℝ (∑ j,w j • p j)).comp
      (ContinuousLinearMap.fst ℝ E E)).comp J)-
      (∑ j,w j • (((-innerSL ℝ (p j)).comp
        (ContinuousLinearMap.fst ℝ E E)).comp (K j)))=0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    simp only [sub_apply,ContinuousLinearMap.comp_apply,J,K,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      sum_apply,smul_apply,smul_eq_mul,neg_apply,
      innerSL_apply_apply,zero_apply,sum_inner,real_inner_smul_left,
      mul_neg,Finset.sum_neg_distrib,sub_self]
  rw [hl] at HT
  refine ⟨pullBilinear B J-∑ j,w j • pullBilinear (C j) (K j),?_,?_⟩
  · convert! HT using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=i <;> simp [K,hj]
  · intro a d
    simp only [sub_apply,sum_apply,smul_apply,smul_eq_mul,
      pullBilinear_apply,J,K,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    rw [hB,real_inner_smul_right]
    have HC : ∀ j, C j (a,(if j=i then ContinuousLinearMap.snd ℝ E E else 0) (a,d))
        (a,(if j=i then ContinuousLinearMap.snd ℝ E E else 0) (a,d))=
        r j a-(if j=i then 2*inner ℝ a d else 0) := by
      intro j
      by_cases hj : j=i <;> simp only [hj,ite_true, if_true,ite_false, if_false,
        ContinuousLinearMap.coe_snd',zero_apply,hC,inner_zero_right,mul_zero]
    simp_rw [HC,mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) :=
  hmtw.global_support hv (active_hull_subset_normalSubdifferential hv x hp)

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
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

lemma WeakMTW.hopfPole_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    hopfLax t u z=u (hopfPole (n := n) t u z)+cost (hopfPole (n := n) t u z) z/t := by
  rw [hdual.1] at hu ⊢
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  have He : hopfPole (n := n) t (cTransform v) z=q.1.1 := by
    change hopfPole (n := n) t (cTransform v) (graphProjection (cTransform v) t q)=q.1.1 at H
    rwa [hq] at H
  rw [He,←hq]
  exact hmtw.hopfLax_graph_value hv ht ht1 q

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActualPoleJet
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

lemma WeakMTW.actualPole_fixed_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    hopfLax t u (riemannianExp x (t • p))=u x+t*(‖p‖^2/2) ∧
    ∀ᶠ q in 𝓝 p, hopfLax t u (riemannianExp x (t • q))≤
      hopfLax t u (riemannianExp x (t • p))+t*(‖q‖^2/2-‖p‖^2/2) := by
  have He := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • p))
  rw [hpole] at He
  have hb : cost x (riemannianExp x (t • p))/t=t*(‖p‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using prefixAction_axis hp
  rw [hb] at He
  refine ⟨He,?_⟩
  filter_upwards [prefixAction_axis_near hp] with q hq
  have H := hopfLax_le hu t (riemannianExp x (t • q)) x
  have hbq : cost x (riemannianExp x (t • q))/t=t*(‖q‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using hq
  rw [hbq] at H
  rw [He]
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualTransferInequality
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma single_move_weighted_sum {E : Type*} [Zero E] (w : ι → ℝ) (i : ι)
    (ψ : ι → E → ℝ) (d : E) :
    ∑ j,w j*ψ j (if j=i then d else 0)-∑ j,w j*ψ j 0 =
      w i*(ψ i d-ψ i 0) := by
  rw [←Finset.sum_sub_distrib]
  have he : ∀ j, w j*ψ j (if j=i then d else 0)-w j*ψ j 0 =
      if j=i then w i*(ψ i d-ψ i 0) else 0 := by
    intro j; by_cases hj:j=i <;> simp [hj,mul_sub]
  simp_rw [he]
  simp

lemma WeakMTW.actual_transfer_inequality (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (ht1 : t<1) (hs : 0 < s) (hs1 : s<1) {x:M}
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap u v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    (ha : ContinuousAt a p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    let S := fun h : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x =>
      prefixDefect x t p (h.1,w i • h.2)-
        ∑ j,w j*splitDefect x s (pj j) (h.1,if j=i then h.2 else 0)
    let f := fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • (p+w i • d)))-t*(‖p+w i • d‖^2/2)
    let ψ := fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2
    ∀ᶠ d in 𝓝 (0:TangentSpace 𝓘(ℝ,Model n) x),
      S (a (p+w i • d),d)-S 0-(f d-f 0)≤w i*(ψ d-ψ 0) := by
  dsimp only
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let ψ : ι → V → ℝ := fun j d => v (riemannianExp x (pj j+d))+‖pj j+d‖^2/2
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have hlimit := ((continuous_riemannianExp x).continuousAt.comp ha).tendsto.congr' harep
    simpa only [Function.comp_apply, ha0, riemannianExp_zero] using eq_of_tendsto_nhds hlimit
  have hf0 := (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).1
  have hψ0 : ∀ j, ψ j 0 = -u x := by
    intro j
    have H := hactive j
    have hm := hmin j
    change dist x (riemannianExp x (pj j))=‖pj j‖ at hm
    rw [contactGap,cost,hm] at H
    dsimp [ψ]; simp only [add_zero] <;> linarith
  have hD0 : ∀ j,splitDefect x s (pj j) 0=0 := by
    intro j
    simp only [splitDefect,Prod.fst_zero,Prod.snd_zero,add_zero,
      splitEndpointCost_axis hs hs1 (hleft j) (hright j),sub_self]
  have hB0 : prefixDefect x t p 0=0 := by
    simp only [prefixDefect,Prod.fst_zero,Prod.snd_zero,add_zero,prefixAction_axis hp,sub_self]
  have hq : Tendsto (fun d:V => p+w i • d) (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt,smul_zero,add_zero] using
      (show ContinuousAt (fun d:V => p+w i • d) 0 from by fun_prop)
  filter_upwards [hq.eventually harep] with d hd
  have henv := hmtw.hopfPole_minimizer hu hv hdual ht ht1
    (riemannianExp x (t • (p+w i • d)))
  rw [←hd] at henv
  let a' := a (p+w i • d)
  let δ : ι → V := fun j => if j=i then d else 0
  have hineq : -u (riemannianExp x a')≤∑ j,w j*(splitEndpointCost x s (a',pj j+δ j)+
      v (riemannianExp x (pj j+δ j))) := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left
        (show -u (riemannianExp x a')≤ splitEndpointCost x s (a',pj j+δ j)+
          v (riemannianExp x (pj j+δ j)) from by
          have HG := dualPair_gap_nonneg hv hdual (riemannianExp x a')
            (riemannianExp x (pj j+δ j))
          have HC := normalCost_le_splitNormalAction x (pj j+δ j) a' (pj j+δ j) hs hs1
          dsimp only [contactGap] at HG
          change cost (riemannianExp x a') (riemannianExp x (pj j+δ j))≤
            splitEndpointCost x s (a',pj j+δ j) at HC
          linarith) (hw j))
    simpa only [←Finset.sum_mul,hsum,one_mul] using H
  have hsumψ := single_move_weighted_sum w i ψ d
  have hψsum : ∑ j,w j*ψ j 0 = -u x := by
    simp only [hψ0,←Finset.sum_mul,hsum,one_mul]
  rw [hψsum,hψ0 i] at hsumψ
  have hψi0 := hψ0 i
  dsimp only [ψ] at hψi0
  simp only [add_zero] at hψi0
  have hψi0w := congrArg (fun z:ℝ => w i*z) hψi0
  simp only [Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero,ite_self,
    ←Prod.zero_eq_mk,hD0,mul_zero,Finset.sum_const_zero,hB0,sub_zero,hf0]
  dsimp only [prefixDefect,splitDefect,prefixAction] at *
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib,mul_add] at hineq ⊢
  have Hψ : ∑ j,w j*ψ j (δ j)=
      (∑ j,w j*v (riemannianExp x (pj j+δ j)))+∑ j,w j*(‖pj j+δ j‖^2/2) := by
    dsimp only [ψ]; simp only [mul_add,Finset.sum_add_distrib]
  change (∑ j,w j*ψ j (δ j))- -u x=w i*(ψ i d- -u x) at hsumψ
  rw [Hψ] at hsumψ
  dsimp only [ψ] at hsumψ
  dsimp only [a',δ] at hineq hsumψ
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_ActualLowerJet
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.actual_active_lower_jet (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0<w j) (hsum : ∑ j,w j=1) (i : ι)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap u v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let p : V := ∑ j,w j • pj j
  have hs : 0 < s := ht.trans hts
  have ht1 : t<1 := hts.trans hs1
  have hsub : range pj ⊆ activeLogs v x := by
    rintro _ ⟨j,rfl⟩
    exact ⟨hmin j,by rw [←hdual.1]; exact hactive j⟩
  have hID : ∀ q∈convexHull ℝ (range pj),t • q∈injectivityDomain x := by
    intro q hq
    exact contracted_minimizer_mem_injectivityDomain
      (hmtw.active_hull_global_support hv (convexHull_mono hsub hq)).1 ht ht1
  have hpH : p∈convexHull ℝ (range pj) :=
    (convex_convexHull ℝ (range pj)).sum_mem (fun j _ => (hw j).le) hsum
      (fun j _ => subset_convexHull ℝ _ (mem_range_self j))
  have hp := hID p hpH
  have hkernel : ∀ j, R (pj j-p)=0 := fun j =>
    hmtw.actualPole_kernel hu hv hdual ht ht1 hs hs1 hp (hmin j) (hactive j)
      (hleft j) (hright j) ha ha0 harep
  have hsym := (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).2.2
  obtain ⟨B,hB,hBdiag⟩ := prefixDefect_taylor ht.ne' hp
  have HC := fun j => splitDefect_taylor hs hs1 (hleft j) (hright j)
  choose C hC hCdiag using HC
  obtain ⟨D,hD,hDdiag⟩ := weighted_defect_taylor w pj i hB hC hBdiag hCdiag
  let J : V →L[ℝ] V := w i • ContinuousLinearMap.id ℝ V
  have hres := (hmtw.actualPole_residual_taylor hu hv hdual ht ht1 hp ha ha0 harep).comp_linear J
  have hq : HasFDerivAt (fun d:V => p+w i • d) J 0 := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0:V)).const_smul (w i)).const_add p
  have hA : HasFDerivAt (fun d:V => (a (p+w i • d),d))
      ((R.comp J).prod (ContinuousLinearMap.id ℝ V)) 0 := by
    have HA := (show HasFDerivAt a R (p+w i • (0:V)) from by
      simpa only [smul_zero,add_zero] using ha).comp 0 hq
    exact HA.prodMk (hasFDerivAt_id (𝕜 := ℝ) (0:V))
  have hA0 : (a (p+w i • (0:V)),(0:V))=0 := by
    change (a (p+w i • (0:V)),(0:V))=(0,0)
    rw [smul_zero,add_zero,show a p=0 from ha0]
  have Hineq := hmtw.actual_transfer_inequality hu hv hdual ht ht1 hs hs1 pj w
    (fun j => (hw j).le) hsum i hp hmin hactive hleft hright ha.continuousAt ha0 harep
  have Hlow := lowerTaylor_of_stationary_transfer hD hA hA0 hres (hw i)
    (by simpa only [ContinuousLinearMap.zero_comp,zero_apply,sub_zero,J,
      smul_apply,ContinuousLinearMap.id_apply] using Hineq)
  apply Hlow.mono_diagonal
  intro d
  let r : V := R (J d)
  have horth : ∀ j,inner ℝ r (pj j-p)=0 := by
    intro j
    change inner ℝ (R (J d)) (pj j-p)=0
    rw [hsym,hkernel,inner_zero_right]
  have hQ : 0≤hessianValue x (t • p) r/t-∑ j,w j*(hessianValue x (s • pj j) r/s) := by
    by_cases hr : r=0
    · rw [hr]
      simp only [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian (hleft _),
        map_zero,zero_div,mul_zero,Finset.sum_const_zero,sub_zero,le_refl]
    · exact sub_nonneg.mpr (hmtw.finite_transverse_slack_strict pj w hw hsum hmin ht hts hs1 hID hr horth).le
  change w i*inner ℝ (R d) d ≤ (w i)⁻¹ *
    (D (R (J d),d) (R (J d),d)-(-((innerSL ℝ).comp R)) (J d) (J d))
  rw [hDdiag]
  have hinner : (-((innerSL ℝ).comp R)) (J d) (J d) = -(w i)^2*inner ℝ (R d) d := by
    change -inner ℝ (R (w i • d)) (w i • d)=_
    rw [map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  rw [hinner]
  have H := mul_nonneg (inv_nonneg.mpr (hw i).le) hQ
  have hid : (w i)⁻¹*((w i)^2*inner ℝ (R d) d)=w i*inner ℝ (R d) d := by
    field_simp [(hw i).ne']
  dsimp only [r] at H
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ModifiedActiveLowerJet
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

lemma active_contact_biconjugate {v : M → ℝ} (hv : Continuous v) {x y : M}
    (hactive : contactGap (cTransform v) v x y=0) :
    cTransform (cTransform v) y=v y ∧
      contactGap (cTransform v) (cTransform (cTransform v)) x y=0 := by
  have hle := cTransform_cTransform_le hv y
  have hlo := cTransform_gap_nonneg (continuous_cTransform hv) y x
  rw [contactGap,cost_symm y x] at hlo
  have hact := hactive
  rw [contactGap] at hact
  have he : cTransform (cTransform v) y=v y := by linarith only [hle,hlo,hact]
  exact ⟨he,by simpa only [contactGap,he] using hactive⟩

lemma WeakMTW.modified_active_lower_jet (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0<w j) (hsum : ∑ j,w j=1) (i : ι)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have H := hmtw.actual_active_lower_jet (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht hts hs1 pj w hw hsum i
    hmin (fun j => (active_contact_biconjugate hv (hactive j)).2) hleft hright ha ha0 harep
  apply H.mono
  · simp only [add_zero,(active_contact_biconjugate hv (hactive i)).1]
  · filter_upwards [] with d
    have H := cTransform_cTransform_le hv (riemannianExp x (pj i+d))
    linarith only [H]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma positive_barycentric_restriction {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) :
    let κ := {i : ι // 0<w i}
    Nonempty κ ∧ (∑ i:κ,w i=1) ∧
      (∑ i:κ,w i • p i=∑ i,w i • p i) ∧
      ∀ f : ι → ℝ,∑ i:κ,w i*f i=∑ i,w i*f i := by
  classical
  dsimp only
  have he (f : ι → E) : (∑ i:{i : ι // 0<w i},w i • f i)=∑ i,w i • f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i • f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_smul])
  have hr (f : ι → ℝ) : (∑ i:{i : ι // 0<w i},w i*f i)=∑ i,w i*f i := by
    rw [←Finset.sum_subtype (p := fun i=>0<w i) (Finset.univ.filter (fun i=>0<w i)) (by simp) (fun i=>w i*f i)]
    exact Finset.sum_subset (Finset.filter_subset _ _) (by
      intro i hi hn
      have hi0 : w i=0 := le_antisymm (not_lt.mp (by simpa using hn)) (hw i)
      simp only [hi0,zero_mul])
  have hsum : (∑ i:{i : ι // 0<w i},w i)=1 := by
    simpa only [mul_one] using (hr (fun _=>1)).trans (by simpa only [mul_one] using hs)
  refine ⟨?_,hsum,he p,hr⟩
  by_contra hn
  have : IsEmpty {i : ι // 0<w i} := not_nonempty_iff.mp hn
  simp at hsum

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NonnegativeTransfer
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

lemma WeakMTW.modified_active_lower_jet_nonneg_oai (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι) (hi : 0<w i)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  classical
  let κ := {j : ι // 0<w j}
  have H := positive_barycentric_restriction pj w hw hsum
  let : Nonempty κ := H.1
  have hs : (∑ j:κ,w j)=1 := H.2.1
  have hb : (∑ j:κ,w j • pj j)=∑ j,w j • pj j := H.2.2.1
  exact hmtw.modified_active_lower_jet hv ht hts hs1
    (fun j:κ=>pj j) (fun j:κ=>w j) (fun j=>j.2) hs (⟨i,hi⟩:κ)
    (fun j=>hmin j) (fun j=>hactive j) (fun j=>hleft j) (fun j=>hright j)
    (by simpa only [hb] using ha) (by simpa only [hb] using ha0)
    (by simpa only [hb] using harep)

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg_oai.{u_1, u_2} := @OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg_oai.{u_1, u_2}
