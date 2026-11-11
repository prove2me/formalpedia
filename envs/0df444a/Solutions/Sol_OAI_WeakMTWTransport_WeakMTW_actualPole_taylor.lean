-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.actualPole_taylor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:17.250839+00:00
-- url     : https://prove2.me/submissions/6118c1a2-4fd9-4ccc-aecd-7cc60f96165c

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TaylorPositivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.nonneg_of_localMin {f : E → ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f 0 B)
    (hm : IsLocalMin f 0) (v:E) : 0≤B v v := by
  by_contra hn
  have hB : B v v<0 := lt_of_not_ge hn
  have hv : v≠0 := by
    intro he; subst v; simp at hB
  have hnv : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  let ε := -(B v v)/(4*‖v‖^2)
  have hε : 0<ε := div_pos (neg_pos.mpr hB) (by positivity)
  have hεeq : ε*‖v‖^2 = -(B v v)/4 := by
    dsimp [ε]; field_simp
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually hε).and hm)
  let δ := r/(2*(‖v‖+1))
  have hδ : 0<δ := div_pos hr (by positivity)
  have hδeq : δ*(2*(‖v‖+1))=r := div_mul_cancel₀ _ (by positivity)
  have hmem : δ • v∈Metric.ball (0:E) r := by
    rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
    nlinarith [norm_nonneg v]
  obtain ⟨ht,hm'⟩ := H hmem
  have hbil : B (δ • v) (δ • v)=δ^2*B v v := by
    simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
  have hnorm : ‖δ • v‖^2=δ^2*‖v‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,mul_pow]
  rw [hbil,hnorm] at ht
  simp only [zero_apply,sub_zero] at ht
  have hupper := (abs_le.mp ht).2
  have hmul : ε*(δ^2*‖v‖^2)=δ^2*(-(B v v)/4) := by
    calc
      _=δ^2*(ε*‖v‖^2) := by ring
      _=_ := by rw [hεeq]
  rw [hmul] at hupper
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hδ) hB
  change f 0≤f (δ • v) at hm'
  nlinarith
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PoleJetAlgebra
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

lemma HasSecondTaylor.const_mul {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul] <;> ring
  rw [he]
  exact hf.const_mul_left c

lemma pole_nonneg_of_envelope_taylor {f : E → ℝ} {p : E} {t : ℝ}
    {R : E →L[ℝ] E}
    (hf : HasSecondTaylor (fun h => f (p+h)) (t • innerSL ℝ p)
      (t • innerSL ℝ-(innerSL ℝ).comp R))
    (hupper : ∀ᶠ q in 𝓝 p, f q≤f p+t*(‖q‖^2/2-‖p‖^2/2))
    (d:E) : 0 ≤ inner ℝ (R d) d := by
  have H := ((norm_square_hasSecondTaylor p).const_mul t).sub hf
  have He : t • innerSL ℝ p-t • innerSL ℝ p = (0 : E →L[ℝ] ℝ) := sub_self _
  have HB : t • innerSL ℝ-(t • innerSL ℝ-(innerSL ℝ).comp R)=(innerSL ℝ).comp R :=
    sub_sub_cancel _ _
  rw [He,HB] at H
  have hm : IsLocalMin (fun h => t*(‖p+h‖^2/2)-f (p+h)) 0 := by
    have ht : Tendsto (fun h:E => p+h) (𝓝 0) (𝓝 p) := by
      simpa only [ContinuousAt,add_zero] using
        (show ContinuousAt (fun h:E => p+h) 0 from by fun_prop)
    filter_upwards [ht.eventually hupper] with h hh
    simp only [add_zero]
    linarith
  exact H.nonneg_of_localMin hm d

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondDerivativeTaylor
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasSecondTaylor_of_second_derivative {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {x : E} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hD : HasFDerivAt f' B x) :
    HasSecondTaylor (fun h => f (x+h)) (f' x) B := by
  have hs : ∀ v w, B v w=B w v := second_derivative_symmetric_of_eventually hf hD
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).def hε
  have hnear : ∀ᶠ h : E in 𝓝 0, HasFDerivAt f (f' (x+h)) (x+h) := by
    exact (show ContinuousAt (fun h : E => x+h) 0 from continuousAt_const.add continuousAt_id).eventually
      (by simpa only [add_zero] using hf)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hnear.and hrem)
  let R : E → ℝ := fun h => f (x+h)-f x-f' x h-B h h/2
  have hR0 : R 0=0 := by simp [R]
  have hdR : ∀ z ∈ Metric.ball (0:E) r,
      HasFDerivAt R (f' (x+z)-f' x-B z) z := by
    intro z hz
    have hshift : HasFDerivAt (fun h : E => x+h) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_add x
    have hbase := (hball hz).1.comp (f := fun h : E => x+h) z hshift
    have hquad : HasFDerivAt (fun v : E => B v v/2) (B z) z := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1/2:ℝ)
      have he : (fun v : E => B v v/2)=((1/2:ℝ) • fun v : E => B v v) := by
        ext v; simp only [Pi.smul_apply,smul_eq_mul] <;> ring
      rw [he]
      apply H.congr_fderiv
      ext v
      simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v z]
      ring
    convert! ((hbase.sub_const (f x)).sub (f' x).hasFDerivAt).sub hquad using 1
    all_goals try with_reducible_and_instances rfl
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  have hsub : Metric.closedBall (0:E) ‖h‖ ⊆ Metric.ball (0:E) r := by
    intro z hz
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hz hh ⊢
    exact lt_of_le_of_lt hz hh
  have H := (convex_closedBall (0:E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hdR z (hsub hz)).hasFDerivWithinAt)
    (show ∀ z ∈ Metric.closedBall (0:E) ‖h‖, ‖f' (x+z)-f' x-B z‖≤ε*‖h‖ from by
      intro z hz
      exact (hball (hsub hz)).2.trans
        (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hε.le))
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show h ∈ Metric.closedBall (0:E) ‖h‖ by simp)
  simpa only [hR0,sub_zero,R,add_zero,pow_two,Real.norm_eq_abs,abs_pow,
    abs_norm,abs_mul,mul_assoc] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_EnvelopePole
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

lemma envelope_pole_second_derivative {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E} {t : ℝ}
    (hC : ContDiffAt ℝ 2 C (0,p))
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q))
    (hqq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (0,d) (0,e)=t*inner ℝ d e)
    (haq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (d,0) (0,e) = -inner ℝ d e) :
    HasFDerivAt (fderiv ℝ f) (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  let I : E →L[ℝ] E×E := (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)
  let G : E → E →L[ℝ] ℝ := fun q => (fderiv ℝ C (a q,q)).comp I
  have hmap := ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hC' : ContDiffAt ℝ 2 C (a p,p) := by rwa [ha0]
  have hd := ((hC'.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun q => (a q,q)) p hmap
  have hG := hd.clm_comp (hasFDerivAt_const I p)
  have heq : fderiv ℝ f =ᶠ[𝓝 p] G := by
    have hn := hmap.continuousAt.eventually (hC'.eventually (by norm_num))
    filter_upwards [hf,hsupport,hn] with q hq hs hreg
    let g : E → ℝ := fun v => f q+C (a q,v)-C (a q,q)
    have hD := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (a q,v)) q
      ((hasFDerivAt_const (a q) q).prodMk (hasFDerivAt_id q))
    have hg : HasFDerivAt g (G q) q := by
      convert! (hD.const_add (f q)).sub_const (C (a q,q)) using 1
      all_goals try with_reducible_and_instances rfl
    rw [upper_contact_fderiv hq hg.differentiableAt hs (by dsimp [g] <;> ring)]
    exact hg.fderiv
  apply (hG.congr_of_eventuallyEq heq).congr_fderiv
  ext d e
  simp only [ha0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_zero,
    zero_add,zero_apply,sub_apply,smul_apply,smul_eq_mul,
    innerSL_apply_apply,I]
  have he : (R d,d)=((R d,0):E×E)+(0,d) := by simp
  rw [he,map_add,add_apply,haq,hqq]
  change -inner ℝ (R d) e+t*inner ℝ d e = t*inner ℝ d e-inner ℝ (R d) e
  ring
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

lemma prefixAction_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (a,0) = -inner ℝ p a := by
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => prefixAction x t (u,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixAction,normalCost,div_eq_mul_inv] using H
  have hB := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,p)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A a) heq
  change fderiv ℝ (prefixAction x t) (0,p) (a,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 a at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixAction_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (a,0) = -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (prefixAction x t) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    have hn := (continuous_const_smul t).continuousAt.eventually
      ((isOpen_injectivityDomain x).mem_nhds hp)
    filter_upwards [hn] with v hv
    exact prefixAction_source_gradient ht hv a
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PrefixActionJets
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

lemma prefixAction_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (0,e) = t*inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := ((prefixAction_axis_near hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  let L : V →L[ℝ] V×V := (0:V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine L 0 p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [←H,he]
  have hg : fderiv ℝ (fun v : V => t*(‖v‖^2/2)) =
      (fun v => t • innerSL ℝ v) := by
    funext v
    exact ((half_norm_sq_hasFDerivAt v).const_smul t).fderiv
  rw [hg]
  have hD : HasFDerivAt (fun v : V => t • innerSL ℝ v) (t • innerSL ℝ) p := by
    convert! ((innerSL ℝ).hasFDerivAt (x := p)).const_smul t using 1
    all_goals try with_reducible_and_instances rfl
  rw [hD.fderiv]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
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

lemma WeakMTW.prefix_hopfLax_differentiable (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x:M) :
    Differentiable ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) := by
  intro q
  have he := (contMDiff_riemannianExp_fiber (n := n) x (t • q)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) (fun q => t • q) q :=
    (show ContDiffAt ℝ ∞ (fun q : TangentSpace 𝓘(ℝ,Model n) x => t • q) q from by
      fun_prop).contMDiffAt.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _).comp q
    (he.comp q hl)).differentiableAt

lemma WeakMTW.actualPole_supports (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    (ha : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    ∀ᶠ q in 𝓝 p, ∀ᶠ w in 𝓝 q,
      hopfLax t u (riemannianExp x (t • w))≤
        hopfLax t u (riemannianExp x (t • q))+
          prefixAction x t (a q,w)-prefixAction x t (a q,q) := by
  filter_upwards [ha] with q hq
  apply Filter.Eventually.of_forall
  intro w
  have H := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • q))
  rw [←hq] at H
  have Hw := hopfLax_le hu t (riemannianExp x (t • w)) (riemannianExp x (a q))
  dsimp [prefixAction]
  linarith

lemma WeakMTW.actualPole_second_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasFDerivAt (fderiv ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))))
      (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply envelope_pole_second_derivative hC ha ha0
    (Filter.Eventually.of_forall (hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x))
    (hmtw.actualPole_supports hu hv hdual ht ht1 harep)
    (prefixAction_endpoint_hessian hp)
  intro d e
  rw [hC.isSymmSndFDerivAt (by norm_num) |>.eq]
  rw [prefixAction_mixed ht.ne' hp]
  exact congrArg Neg.neg (real_inner_comm d e)

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

lemma WeakMTW.actualPole_first_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    HasFDerivAt (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) (t • innerSL ℝ p) p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun q => hopfLax t u (riemannianExp x (t • q))
  have hd := hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x p
  have hsup := (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).2
  have hg : HasFDerivAt (fun q : V => f p+t*(‖q‖^2/2-‖p‖^2/2))
      (t • innerSL ℝ p) p := by
    convert! (((half_norm_sq_hasFDerivAt p).sub_const (‖p‖^2/2)).const_smul t).const_add (f p) using 1
    all_goals try with_reducible_and_instances rfl
  have he := upper_contact_fderiv hd hg.differentiableAt hsup (by simp only [sub_self,mul_zero,add_zero]; rfl)
  exact hd.hasFDerivAt.congr_fderiv (he.trans hg.fderiv)

lemma WeakMTW.actualPole_taylor_oai (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) :
    HasSecondTaylor (fun h : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • (p+h))))
      (t • innerSL ℝ p) (t • (innerSL ℝ (E := TangentSpace 𝓘(ℝ,Model n) x))-(innerSL ℝ).comp R) ∧
    (∀ d:TangentSpace 𝓘(ℝ,Model n) x, 0 ≤ inner ℝ (R d) d) ∧
    (∀ d e:TangentSpace 𝓘(ℝ,Model n) x, inner ℝ (R d) e=inner ℝ d (R e)) := by
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have H := harep.self_of_nhds
    rw [ha0,riemannianExp_zero] at H
    exact H.symm
  have hD := hmtw.actualPole_second_derivative hu hv hdual ht ht1 hp ha ha0 harep
  have hnear : ∀ᶠ q in 𝓝 p, HasFDerivAt
      (fun w : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • w)))
      (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ,Model n) x => hopfLax t u (riemannianExp x (t • w))) q) q :=
    Filter.Eventually.of_forall (fun q =>
      (hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x q).hasFDerivAt)
  have HT := hasSecondTaylor_of_second_derivative hnear hD
  rw [(hmtw.actualPole_first_derivative hu hv hdual ht ht1 hp hpole).fderiv] at HT
  refine ⟨HT,pole_nonneg_of_envelope_taylor HT
    (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).2,?_⟩
  intro d e
  have H := second_derivative_symmetric_of_eventually hnear hD d e
  change t*inner ℝ d e-inner ℝ (R d) e=t*inner ℝ e d-inner ℝ (R e) d at H
  rw [real_inner_comm e d,real_inner_comm d (R e)] at H
  linarith

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.actualPole_taylor_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.actualPole_taylor_oai.{u_1}
