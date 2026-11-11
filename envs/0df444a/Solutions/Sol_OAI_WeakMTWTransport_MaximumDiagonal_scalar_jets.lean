-- Prove2me | solution 1 for OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:42:20.051727+00:00
-- url     : https://prove2.me/submissions/00f0fbc3-3b0d-422c-8e8b-64cf3411f3d4

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
import Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_good_centers
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_jensen_undo_short

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Calculus
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma convexOn_of_affine_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S, f x+L (y-x)≤f y) :
    ConvexOn ℝ S f := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  obtain ⟨L,hL⟩ := hs z (hS hx hy ha hb hab)
  have hx' := mul_le_mul_of_nonneg_left (hL x hx) ha
  have hy' := mul_le_mul_of_nonneg_left (hL y hy) hb
  have hzero : a*L (x-z)+b*L (y-z)=0 := by
    rw [←smul_eq_mul a,←smul_eq_mul b,←map_smul,←map_smul,←map_add]
    have he : a • (x-z)+b • (y-z)=0 := by
      rw [smul_sub,smul_sub,←add_sub_add_comm,←add_smul,hab,one_smul]
      exact sub_self z
    rw [he,map_zero]
  change f z≤a*f x+b*f y
  have hc : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  nlinarith [hc]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientDifferential
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

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadraticTaylor_increment (f0 : ℝ) (p : E) (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (h e : E) (t : ℝ) :
    quadraticTaylor f0 p A (h + t • e) - quadraticTaylor f0 p A h =
      t * inner ℝ (p + A h) e + t ^ 2 / 2 * inner ℝ (A e) e := by
  have hs : inner ℝ (A e) h = inner ℝ (A h) e := (hA e h).trans (real_inner_comm _ _)
  simp only [quadraticTaylor, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hs]
  ring

lemma subgradient_directional_bound {f : E → ℝ} {f0 : ℝ} {p h zeta e : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r) (he : ‖e‖ = 1)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    inner ℝ (zeta - p - A h) e ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  have hat : 0 < alpha*r := mul_pos ha hr
  have hz : ‖h + (alpha*r) • e‖ ≤ 2*r := by
    calc
      ‖h + (alpha*r) • e‖ ≤ ‖h‖ + ‖(alpha*r) • e‖ := norm_add_le _ _
      _ = ‖h‖ + alpha*r := by rw [norm_smul_of_nonneg hat.le, he, mul_one]
      _ ≤ 2*r := by nlinarith
  have hxbound := hrem h (by linarith)
  have hzbound := hrem (h + (alpha*r) • e) hz
  have hsg := hsub (h + (alpha*r) • e) (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  have hnormsq : ‖h + (alpha*r) • e‖ ^ 2 ≤ 4*r^2 := by
    nlinarith [norm_nonneg (h + (alpha*r) • e)]
  have hhsq : ‖h‖ ^ 2 ≤ r^2 := by nlinarith [norm_nonneg h]
  have hremdiff : (f (h + (alpha*r) • e) - quadraticTaylor f0 p A (h + (alpha*r) • e)) -
      (f h - quadraticTaylor f0 p A h) ≤ 5*w*r^2 := by
    have h1 := (abs_le.mp hzbound).2
    have h2 := (abs_le.mp hxbound).1
    have h3 := mul_le_mul_of_nonneg_left hnormsq hw
    have h4 := mul_le_mul_of_nonneg_left hhsq hw
    nlinarith
  have hquad := quadraticTaylor_increment f0 p A hA h e (alpha*r)
  have hAe : inner ℝ (A e) e ≤ ‖A‖ := by
    calc
      inner ℝ (A e) e ≤ ‖inner ℝ (A e) e‖ := le_abs_self _
      _ ≤ ‖A e‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  simp only [add_sub_cancel_left, real_inner_smul_right] at hsg
  have hdir : alpha*r * inner ℝ (zeta - p - A h) e ≤
      (alpha*r)^2/2 * ‖A‖ + 5*w*r^2 := by
    simp only [inner_sub_left, inner_add_left] at hquad ⊢
    have hm := mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ (alpha*r)^2/2)
    nlinarith
  apply (mul_le_mul_iff_right₀ hat).mp
  have hcancel : (5*w*r/alpha) * (alpha*r) = 5*w*r^2 := by field_simp
  nlinarith

lemma subgradient_norm_bound {f : E → ℝ} {f0 : ℝ} {p h zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    ‖zeta - p - A h‖ ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  by_cases hzero : zeta - p - A h = 0
  · rw [hzero, norm_zero]
    positivity
  let v := zeta - p - A h
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hzero
  have hd := subgradient_directional_bound hA hr ha ha1 hw hh he hrem hsub
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  have hip : inner ℝ (zeta - p - A h) e = ‖zeta - p - A h‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  exact hip ▸ hd

lemma subgradient_zero_of_quadraticExpansion {f : E → ℝ} {p zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R)
    (hsub : IsSubgradientOn f (Metric.ball 0 R) 0 zeta) : zeta = p := by
  obtain ⟨delta, hdelta, hrem⟩ := hexp 1 zero_lt_one
  let eps := min R delta / 4
  have heps : 0 < eps := by dsimp [eps] <;> positivity
  have hbound (r : ℝ) (hr : r ∈ Ioo 0 eps) :
      ‖zeta - p‖ ≤ ‖A‖ * 1 * r / 2 + 5*1*r/1 := by
    have hrR : 2*r < R := by
      have hh : 4*eps ≤ R := by dsimp [eps] <;> linarith [min_le_left R delta]
      linarith [hr.2]
    have hrdelta : 2*r < delta := by
      have hh : 4*eps ≤ delta := by dsimp [eps] <;> linarith [min_le_right R delta]
      linarith [hr.2]
    have hh := subgradient_norm_bound (p := p) (h := 0) hA hr.1 zero_lt_one
      le_rfl zero_le_one (by simpa using hr.1.le)
      (fun z hz => hrem z (hz.trans_lt hrdelta))
      (fun z hz => hsub z (by
        rw [Metric.mem_ball, dist_zero_right]
        exact (show ‖z‖ ≤ 2 * r from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hrR))
    simpa only [map_zero, sub_zero] using hh
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 eps) := by
    rw [closure_Ioo heps.ne]
    exact ⟨le_rfl, heps.le⟩
  have hcont : Continuous (fun r : ℝ => ‖A‖ * 1 * r / 2 + 5*1*r/1) := by fun_prop
  have hlim := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := ‖zeta-p‖)) hcont.continuousWithinAt hbound
  have hz : ‖zeta-p‖ = 0 := le_antisymm (by simpa using hlim) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma subgradient_uniform_differential {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta → IsSubgradientOn f (Metric.ball 0 R) h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  intro eps heps
  let alpha : ℝ := min 1 (eps / (‖A‖ + 1))
  have ha : 0 < alpha := by dsimp [alpha] <;> positivity
  have ha1 : alpha ≤ 1 := min_le_left _ _
  have hAa : ‖A‖ * alpha ≤ eps := by
    have hh := (le_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp (min_le_right 1 (eps/(‖A‖+1)))
    change alpha * (‖A‖+1) ≤ eps at hh
    nlinarith
  let w : ℝ := eps * alpha / 20
  have hw : 0 < w := by dsimp [w] <;> positivity
  obtain ⟨d, hd, hrem⟩ := hexp w hw
  let delta := min R d / 4
  have hdelta : 0 < delta := by dsimp [delta] <;> positivity
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  by_cases hz : h = 0
  · subst h
    have hzet := subgradient_zero_of_quadraticExpansion hA hexp hR hsub
    simp [hzet]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have hhr : 2*‖h‖ < R := by
    have ht : 4*delta ≤ R := by dsimp [delta] <;> linarith [min_le_left R d]
    linarith
  have hhd : 2*‖h‖ < d := by
    have ht : 4*delta ≤ d := by dsimp [delta] <;> linarith [min_le_right R d]
    linarith
  have hb := subgradient_norm_bound hA hnorm ha ha1 hw.le le_rfl
    (fun z hz => hrem z (hz.trans_lt hhd))
    (fun z hz => hsub z (by
      rw [Metric.mem_ball, dist_zero_right]
      exact (show ‖z‖ ≤ 2 * ‖h‖ from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hhr))
  apply hb.trans
  have hwcalc : 5*w*‖h‖/alpha = eps*‖h‖/4 := by
    dsimp [w]
    field_simp
    ring
  rw [hwcalc]
  have hm := mul_le_mul_of_nonneg_right hAa hnorm.le
  nlinarith

lemma semiconvex_subgradient_iff {f : E → ℝ} {s : Set E} {K : ℝ} {h zeta : E} :
    IsSemiconvexSubgradientOn f s K h zeta ↔
      IsSubgradientOn (fun x => f x + K / 2 * ‖x‖ ^ 2) s h (zeta + K • h) := by
  have heq (y : E) :
      f h + K / 2 * ‖h‖ ^ 2 + inner ℝ (zeta + K • h) (y - h) -
          (f y + K / 2 * ‖y‖ ^ 2) =
      f h + inner ℝ zeta (y-h) - K/2*‖y-h‖^2 - f y := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
      inner_sub_right, real_inner_smul_left]
    rw [real_inner_comm y h]
    ring
  constructor <;> intro hs y hy
  · have hh := hs y hy
    linarith [heq y]
  · have hh := hs y hy
    linarith [heq y]

lemma quadraticExpansion_add_quadratic {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) (K : ℝ) :
    HasQuadraticExpansion (fun x => f x + K / 2 * ‖x‖ ^ 2) p
      (A + K • ContinuousLinearMap.id ℝ E) := by
  intro w hw
  obtain ⟨d, hd, hr⟩ := hexp w hw
  refine ⟨d, hd, fun z hz => ?_⟩
  have heq : (f z + K/2*‖z‖ ^ 2) -
      quadraticTaylor (f 0 + K/2*‖(0 : E)‖ ^ 2) p
        (A + K • ContinuousLinearMap.id ℝ E) z = f z - quadraticTaylor (f 0) p A z := by
    simp only [quadraticTaylor, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
      add_zero, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [heq]
  exact hr z hz

lemma semiconvex_subgradient_uniform_differential {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta →
        IsSemiconvexSubgradientOn f (Metric.ball 0 R) K h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  have hs : ∀ x y : E,
      inner ℝ ((A + K • ContinuousLinearMap.id ℝ E) x) y =
        inner ℝ x ((A + K • ContinuousLinearMap.id ℝ E) y) := by
    intro x y
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hA]
  intro eps heps
  obtain ⟨delta, hdelta, hb⟩ := subgradient_uniform_differential hs
    (quadraticExpansion_add_quadratic hexp K) hR eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  have hhbound := hb h (zeta + K • h) hh (semiconvex_subgradient_iff.mp hsub)
  have heq : zeta + K • h - p - (A + K • ContinuousLinearMap.id ℝ E) h =
      zeta - p - A h := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply]
    abel
  rwa [heq] at hhbound


end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ProximalProducer
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma lower_contact_subgradient_on {f g : E → ℝ} {s : Set E}
    (hc : ConvexOn ℝ s f) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSubgradientOn f s x ((InnerProductSpace.toDual ℝ E).symm g') := by
  intro v hv
  rw [InnerProductSpace.toDual_symm_apply]
  have hp : HasDerivAt (fun t : ℝ => x+t • (v-x)) (v-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-x)).const_add x
  have hd : HasDerivAt (fun t : ℝ => g (x+t • (v-x))) (g' (v-x)) 0 := by
    exact (show HasFDerivAt g g' (x+(0:ℝ) • (v-x)) from by simpa using hg).comp_hasDerivAt 0 hp
  have htend : Tendsto (fun t : ℝ => x+t • (v-x)) (𝓝[>]0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ t : ℝ in 𝓝[>]0,
      t⁻¹*(g (x+t • (v-x))-g x)≤f v-f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),htend.eventually hle] with t ht htf
    have hcv := hc.2 hx hv (by linarith [ht.2] : 0≤1-t) ht.1.le (by ring : 1-t+t=1)
    have he : (1-t) • x+t • v=x+t • (v-x) := by
      simp only [sub_smul,one_smul,smul_sub]; abel
    rw [he] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div,div_le_iff₀ ht.1,heq]
    nlinarith only [hcv,htf]
  have hlim : Tendsto (fun t : ℝ => t⁻¹*(g (x+t • (v-x))-g x))
      (𝓝[>]0) (𝓝 (g' (v-x))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have H := le_of_tendsto hlim hb
  linarith only [H]

lemma lower_contact_semiconvex_subgradient_on {f g : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm g') := by
  rw [semiconvex_subgradient_iff]
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (K/2)
  have hh : (fun z => g z+K/2*‖z‖^2)≤ᶠ[𝓝 x](fun z => f z+K/2*‖z‖^2) := by
    filter_upwards [hle] with z hz
    linarith only [hz]
  have h := lower_contact_subgradient_on hc hx (hg.add hq) (by simp only [Pi.add_apply,heq]) hh
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  ext z
  simp only [add_apply,smul_apply,
    InnerProductSpace.toDual_apply_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma kernel_minimum_semiconvex_subgradient {f k : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {k' : E →L[ℝ] ℝ} (hk : HasFDerivAt k k' x)
    (hmin : ∀ᶠ y in 𝓝 x, f x+k x≤f y+k y) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm (-k')) := by
  apply lower_contact_semiconvex_subgradient_on hc hx
    (hk.neg.const_add (f x+k x)) (by simp only [Pi.neg_apply] <;> ring)
  filter_upwards [hmin] with y hy
  simp only [Pi.neg_apply]
  linarith only [hy]

omit [CompleteSpace E] in
lemma semiconvex_subgradient_eq_at_expansion {f : E → ℝ} {x p ξ : E}
    {A : E →L[ℝ] E} (hA : ∀ v w,inner ℝ (A v) w=inner ℝ v (A w))
    (hexp : HasQuadraticExpansion (fun h => f (x+h)) p A)
    {r : ℝ} (hr : 0 < r) (K : ℝ)
    (hsub : IsSemiconvexSubgradientOn f (Metric.ball x r) K x ξ) : ξ=p := by
  obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hr K 1 zero_lt_one
  have hh := H 0 ξ (by simpa using hd) (by
    intro w hw
    have hw' : x+w∈Metric.ball x r := by
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
    simpa only [add_zero,sub_zero,add_sub_cancel_left] using hsub (x+w) hw')
  have hn : ‖ξ-p‖≤0 := by simpa only [map_zero,sub_zero,norm_zero,mul_zero] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
end WeakMTWTransport

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

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateRaise_contDiffAt {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×(Model n →L[ℝ] ℝ) =>
      (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.1 hg
  exact contDiffAt_fst.prodMk ((hi.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_CotangentFlow
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

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_contDiffAt {a:M} {q:Model n × Model n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (phaseLower a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  exact contDiffAt_fst.prodMk ((hg.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_raise {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : phaseLower a (phaseRaise a q)=q := by
  exact Prod.ext rfl ((riemannianCoordinateMetric_isInvertible hq).self_apply_inverse q.2)

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_zero {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : coordinatePhaseFlow a (0,q)=q := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  dsimp only [coordinatePhaseFlow]
  rw [neg_zero,sprayFlow_zero,χ.right_inv ht]
  exact phaseLower_raise hq

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_contDiffAt {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (coordinatePhaseFlow a) (0,q) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)).contMDiffAt
    ((isOpen_extChartAt_target _).mem_nhds ht)
  have hr:ContDiffAt ℝ ∞ (phaseRaise a) q := coordinateRaise_contDiffAt hq
  have hinput := hi.comp (f:=fun p:ℝ×Phase n=>phaseRaise a p.2) (0,q)
    (hr.comp (0,q) contDiffAt_snd).contMDiffAt
  have hf := contMDiff_sprayFlow.contMDiffAt.comp (f:=fun p:ℝ×Phase n=>
    (-p.1,χ.symm (phaseRaise a p.2))) (0,q)
    (contDiffAt_fst.neg.contMDiffAt.prodMk hinput)
  have he:sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))=χ.symm (phaseRaise a q) := by
    rw [neg_zero,sprayFlow_zero]
  have hc:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n × Model n) ∞ χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))) := by
    rw [he]
    exact contMDiffAt_extChartAt' (by simpa only [χ,extChartAt_source] using χ.map_target ht)
  have hout := (hc.comp (f:=fun p:ℝ×Phase n=>
    sprayFlow (-p.1) (χ.symm (phaseRaise a p.2))) (0,q) hf).contDiffAt
  have hbase:(χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q)))).1∈
      (extChartAt 𝓘(ℝ,Model n) a).target := by
    rw [he,χ.right_inv ht]; exact hq
  exact (phaseLower_contDiffAt hbase).comp (0,q) hout

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_PhaseContact
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

lemma coordinatePhaseFlow_of_minimizer {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t≤1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1) :
    coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)) =
      phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let w:TangentBundle 𝓘(ℝ,Model n) M:=⟨x,p⟩
  let z:=sprayFlow t w
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  let η:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hf:=hopfLax_derivative_of_minimizer hu hp ht ht1 he hd
  have hf':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) z.1 (innerSL ℝ ((1:ℝ) • z.2)) := by
    simpa only [one_smul] using hf
  have hh:=coordinate_gradient_of_hasMFDerivAt z hz (hopfLax t u) 1 hf'
  simp only [one_smul] at hh
  have hi:=riemannianCoordinateMetric_isInvertible (χ.map_source hz)
  have hraise:phaseRaise a (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))=η z := by
    apply Prod.ext
    · rfl
    · change (riemannianCoordinateMetric a (χ z.1)).inverse _=(η z).2
      rw [hh.fderiv,hi.inverse_apply_self]
  change phaseLower a (η (sprayFlow (-t) (η.symm (phaseRaise a
    (χ z.1,fderiv ℝ (fun q=>hopfLax t u (χ.symm q)) (χ z.1))))))=phaseLower a (η w)
  rw [hraise,η.left_inv ((tangent_chart_source_iff _ _).mpr hz)]
  rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

omit [Nonempty M] in
lemma divided_kernel_gradient {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {t:ℝ} (ht:t≠0) (hp:t • p∈injectivityDomain x)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    HasFDerivAt (fun y=>cost ((extChartAt 𝓘(ℝ,Model n) a).symm y)
      (riemannianExp x (t • p))/t)
      (-(phaseLower a (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M))).2)
      (extChartAt 𝓘(ℝ,Model n) a x) := by
  have hg:=cost_start_gradient_of_injectivityDomain hp
  have hg':HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun y=>cost y (riemannianExp x (t • p))) x
      (innerSL ℝ ((-t) • p)) := by simpa only [neg_smul] using hg
  have hc:=coordinate_gradient_of_hasMFDerivAt (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)
    hx (fun y=>cost y (riemannianExp x (t • p))) (-t) hg'
  simp only [div_eq_mul_inv]
  apply (hc.mul_const t⁻¹).congr_fderiv
  ext v
  simp only [smul_apply, neg_apply,smul_eq_mul,phaseLower]
  field_simp
  rfl

lemma phase_contact_semiconvex {a x:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    {u:M → ℝ} (hu:Continuous u) (hp:p∈minimizingVectors x)
    {t:ℝ} (ht:0<t) (ht1:t<1)
    (he:hopfLax t u (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=
      u x+cost x (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:(sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1)
    {s:Set (Model n)} {K:ℝ}
    (hxs:extChartAt 𝓘(ℝ,Model n) a x∈s)
    (hsem:ConvexOn ℝ s (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+K/2*‖y‖^2)) :
    let Q:=coordinatePhaseFlow a (t,
      extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1,
      fderiv ℝ (fun z=>hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z))
        (extChartAt 𝓘(ℝ,Model n) a (sprayFlow t (⟨x,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1))
    Q.1=extChartAt 𝓘(ℝ,Model n) a x ∧
      IsSemiconvexSubgradientOn (fun y=>u ((extChartAt 𝓘(ℝ,Model n) a).symm y)) s K Q.1
        ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  dsimp only
  rw [coordinatePhaseFlow_of_minimizer hu hp ht ht1.le he hz hd]
  refine ⟨rfl,?_⟩
  have hk:=divided_kernel_gradient ht.ne' (contracted_minimizer_mem_injectivityDomain hp ht ht1) hx
  have hmin:∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,Model n) a x),
      u ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm (extChartAt 𝓘(ℝ,Model n) a x))
          (riemannianExp x (t • p))/t ≤
      u ((extChartAt 𝓘(ℝ,Model n) a).symm y)+
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm y) (riemannianExp x (t • p))/t := by
    apply Eventually.of_forall
    intro y
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,riemannianExp_smul,←he]
    exact hopfLax_le hu t _ _
  have HH:=kernel_minimum_semiconvex_subgradient hsem hxs hk hmin
  simp only [neg_neg] at HH
  convert HH using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ModifiedPhase
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

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiable_of_fixed_chart {a z:M} {f:M → ℝ}
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>f ((extChartAt 𝓘(ℝ,Model n) a).symm q))
      (extChartAt 𝓘(ℝ,Model n) a z)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z := by
  have H:=hd.hasFDerivAt.hasMFDerivAt.comp z
    (mdifferentiableAt_extChartAt (I:=𝓘(ℝ,Model n))
      (show z∈(chartAt (Model n) a).source from by simpa only [extChartAt_source] using hz)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) a).left_inv hy]

lemma WeakMTW.modified_phase_subgradient (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφc:Continuous φ)
    {a y z:M} {l τ:ℝ} (hφ:HasDerivAt φ l (v y))
    (hl:0<l) (hl1:l<1) (hτ:0<τ) (hτ1:τ<1)
    (hval:hopfLax τ (fun w=>φ (v w)) z=φ (v y)+cost y z/τ)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hz:z∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd:DifferentiableAt ℝ (fun q=>hopfLax τ (fun w=>φ (v w))
      ((extChartAt 𝓘(ℝ,Model n) a).symm q)) (extChartAt 𝓘(ℝ,Model n) a z))
    {s:Set (Model n)} {K:ℝ} (hys:extChartAt 𝓘(ℝ,Model n) a y∈s)
    (hsem:ConvexOn ℝ s (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    let Q:=coordinatePhaseFlow a (τ,extChartAt 𝓘(ℝ,Model n) a z,
      fderiv ℝ (fun q=>hopfLax τ (fun w=>φ (v w)) ((extChartAt 𝓘(ℝ,Model n) a).symm q))
        (extChartAt 𝓘(ℝ,Model n) a z))
    Q.1=extChartAt 𝓘(ℝ,Model n) a y ∧
      IsSemiconvexSubgradientOn (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))) s K
        (extChartAt 𝓘(ℝ,Model n) a y) ((InnerProductSpace.toDual ℝ (Model n)).symm Q.2) := by
  obtain ⟨p,_,he,_,_,hp⟩:=hmtw.exists_center_ray_of_minimizer hu hv hdual hφc hφ hl hl1 hτ hτ1 hval
  have he':(sprayFlow τ (⟨y,p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rwa [riemannianExp_smul] at he
  have HH:=phase_contact_semiconvex (hφc.comp hv.continuous)
    (injectivityDomain_subset_minimizingVectors y hp) hτ hτ1
    (he'.symm ▸ hval) hy (he'.symm ▸ hz)
    (he'.symm ▸ mdifferentiable_of_fixed_chart hz hd) hys hsem
  rw [he'] at HH
  dsimp only at HH ⊢
  exact ⟨HH.1,HH.1 ▸ HH.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenPhaseGradient
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.jensen_phase_gradient (hmtw:WeakMTW (n:=n) (M:=M))
    {u v w:M → ℝ} (hu:Continuous u) {L:ℝ≥0} (hv:LipschitzWith L v)
    (hdual:IsCostDualPair u v) {φ:ℝ → ℝ} (hφ:ContDiff ℝ ∞ φ)
    (hslope:∀y:M,0<deriv φ (v y) ∧ deriv φ (v y)<1)
    {a c:M} {N:Set (Model n)} {t:ℝ} (ht:0<t) (ht1:t<1)
    (J:JensenSamplesAt w (fun y=>φ (v y)) t a c N) (i:ℕ)
    (hi:J.z i∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {p:Model n} {A:Model n →L[ℝ] Model n} {r K:ℝ} (hr:0 < r)
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hexp:HasQuadraticExpansion (fun h=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm
      (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))+h)))) p A)
    (hsem:ConvexOn ℝ (Metric.ball (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z i))) r)
      (fun q=>φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm q))+K/2*‖q‖^2)) :
    (coordinatePhaseFlow a (1-t,J.z i,fderiv ℝ
      (chartCenterEnvelope (fun y=>φ (v y)) t a) (J.z i))).2=innerSL ℝ p := by
  let χ:=extChartAt 𝓘(ℝ,Model n) a
  have H:=hmtw.modified_phase_subgradient
    (s:=Metric.ball (χ (J.Y (J.z i))) r) hu hv hdual hφ.continuous
    ((hφ.differentiable (by simp)).differentiableAt.hasDerivAt (x:=v (J.Y (J.z i))))
    (hslope _).1 (hslope _).2 (sub_pos.mpr ht1) (by linarith : 1-t<1)
    (((J.actual (J.z i) (J.sampleInRegion i)).2.2.1 (J.Y (J.z i))).mpr rfl)
    (J.samples i).1 (χ.map_target hi)
    (by rw [χ.right_inv hi]; exact J.centerDifferentiable _ (J.sampleInRegion i))
    (Metric.mem_ball_self hr) hsem
  simp only [(extChartAt 𝓘(ℝ,Model n) a).right_inv hi] at H
  have HH:=semiconvex_subgradient_eq_at_expansion hA hexp hr K H.2
  apply (InnerProductSpace.toDual ℝ (Model n)).symm.injective
  change _=(InnerProductSpace.toDual ℝ (Model n)).symm ((InnerProductSpace.toDual ℝ (Model n)) p)
  rw [(InnerProductSpace.toDual ℝ (Model n)).symm_apply_apply]
  exact HH

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phase_gradient_tendsto {a:M} {t:ℕ → ℝ} {z:ℕ → Model n}
    {g:ℕ → Model n →L[ℝ] ℝ} {g0:Model n →L[ℝ] ℝ} {p:ℕ → Model n}
    (ht:Tendsto t atTop (𝓝 1))
    (hz:Tendsto z atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hg:Tendsto g atTop (𝓝 g0))
    (hp:∀ᶠ k in atTop,(coordinatePhaseFlow a (1-t k,z k,g k)).2=innerSL ℝ (p k)) :
    Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g0) := by
  have hτ:Tendsto (fun k=>1-t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub ht :
      Tendsto (fun k=>(1:ℝ)-t k) atTop (𝓝 (1-1)))
  have H:=((coordinatePhaseFlow_contDiffAt (q:=(extChartAt 𝓘(ℝ,Model n) a a,g0))
    (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a)).continuousAt.tendsto).comp
    (hτ.prodMk_nhds (hz.prodMk_nhds hg))
  have HH:=H.snd_nhds
  rw [coordinatePhaseFlow_zero (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a)] at HH
  exact HH.congr' hp
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Inner
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

lemma convexOn_of_quadratic_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (B : ℝ)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y) :
    ConvexOn ℝ S (fun x => f x+B*‖x‖^2) := by
  apply convexOn_of_affine_lower_supports hS
  intro x hx
  obtain ⟨L,hL⟩ := hs x hx
  refine ⟨L+(2*B) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hL y hy
  simp only [_root_.add_apply,_root_.smul_apply,innerSL_apply_apply,inner_sub_right,
    smul_eq_mul,real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real] at H
  have hi : inner ℝ y x=inner ℝ x y := real_inner_comm _ _
  rw [hi] at H
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ParametricSemiconvex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma scalar_family_uniform_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    (a b K : ℝ) (hK : 0≤K) (L : ℝ≥0) :
    ∃ C>0,∀ p∈Kp,∀ S : Set E,Convex ℝ S → ∀ f:E → ℝ,
      LipschitzOnWith L f S → (∀ x∈S,f x∈Icc a b) →
      (∀ x∈S,∃ l:E →L[ℝ] ℝ,∀ y∈S,f x+l (y-x)-K*‖y-x‖^2≤f y) →
      ConvexOn ℝ S (fun x=>Φ (p,f x)+C/2*‖x‖^2) := by
  let dd := fun q:P×ℝ=>fderiv ℝ (fun s=>Φ (q.1,s)) q.2
  let hh := fun q:P×ℝ=>fderiv ℝ (fderiv ℝ (fun s=>Φ (q.1,s))) q.2
  have hdd : Continuous dd := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  have hhh : Continuous hh := continuous_iff_continuousAt.mpr (fun q=>
    (ContDiffAt.partial_snd_fderiv_two (f := fun p s=>Φ (p,s)) (hΦ.contDiffAt (x := q))).continuousAt)
  obtain ⟨A0,hA0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := dd) hdd.continuousOn
  obtain ⟨B0,hB0⟩ := (hKp.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn (f := hh) hhh.continuousOn
  let A := max A0 0
  let B := max B0 0
  have hA : 0≤A := le_max_right _ _
  have hB : 0≤B := le_max_right _ _
  let C := 2*(A*K+B*(L:ℝ)^2+1)
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro p hp S hS f hlip hrange hs
  let φ := fun s=>Φ (p,s)
  have hφ : ContDiff ℝ 2 φ := (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply convexOn_of_quadratic_lower_supports hS (C/2)
  intro x hx
  obtain ⟨l,hl⟩ := hs x hx
  refine ⟨deriv φ (f x) • l,?_⟩
  intro y hy
  have H := first_order_remainder_le_of_hessian_bound (convex_Icc a b) hB
    (fun z hz=>hφ.contDiffAt) (fun z hz=>by exact (hB0 (p,z) ⟨hp,hz⟩).trans (le_max_left _ _))
    (hrange x hx) (hrange y hy)
  rw [fderiv_eq_deriv_mul] at H
  have Hlow := (abs_le.mp H).1
  have Hf := mul_le_mul_of_nonneg_left (hl y hy) ((hmono p hp).deriv_nonneg (x := f x))
  have Hlip := hlip.dist_le_mul y hy x hx
  rw [dist_eq_norm,dist_eq_norm] at Hlip
  have Hsq := sq_le_sq₀ (norm_nonneg (f y-f x)) (by positivity : 0≤(L:ℝ)*‖y-x‖) |>.mpr Hlip
  have HB := mul_le_mul_of_nonneg_left Hsq hB
  have HA : deriv φ (f x)≤A := by
    have hh0 := hA0 (p,f x) ⟨hp,hrange x hx⟩
    have hh1 : |deriv φ (f x)|≤A0 := by
      simpa only [dd,←norm_deriv_eq_norm_fderiv,Real.norm_eq_abs] using hh0
    exact (le_abs_self _).trans (hh1.trans (le_max_left _ _))
  have HK := mul_le_mul_of_nonneg_right HA (mul_nonneg hK (sq_nonneg ‖y-x‖))
  simp only [_root_.smul_apply,smul_eq_mul]
  dsimp only [C]
  nlinarith [sq_nonneg ‖y-x‖]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_LocalMetricCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
local notation "𝒥" => 𝓘(ℝ,E)

lemma exists_lipschitzOn_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ball (extChartAt 𝓘(ℝ,E) x x) r ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,E) x).symm
        (ball (extChartAt 𝓘(ℝ,E) x x) r) := by
  let (y : E) : ENorm (TangentSpace 𝒥 y →L[ℝ]
      TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)) :=
    inferInstanceAs (ENorm (E →L[ℝ] TangentSpace 𝒥 ((extChartAt 𝒥 x).symm y)))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝒥 x
  obtain ⟨r,hrpos,hr⟩ : ∃ r > 0,
      ball (extChartAt 𝒥 x x) r ⊆ (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} := by
    have hh := inter_mem (extChartAt_target_mem_nhdsWithin (I := 𝒥) x) hC
    have hh' : (extChartAt 𝒥 x).target ∩
        {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)} ∈
        𝓝 (extChartAt 𝒥 x x) := by
      simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hh ⊢
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    exact Metric.mem_nhds_iff.mp hh'
  refine ⟨C,r,hrpos,fun y hy => (hr hy).1,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := (extChartAt 𝒥 x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝒥 x).target ∩
      {y : E | ‖mfderiv[range 𝒥] (extChartAt 𝒥 x).symm y‖ₑ < (C : ℝ≥0∞)}) := by
    simp only [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap,η]
    exact ((convex_ball _ _).segment_subset hu hv).trans hr
  simp only [preimage_inter,subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hh : riemannianEDist 𝒥 ((extChartAt 𝒥 x).symm u) ((extChartAt 𝒥 x).symm v) ≤
      pathELength 𝒥 γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝒥)]
  apply hh.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hd1 : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝒥] (extChartAt 𝒥 x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hd 1)
  rw [hd1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_FamilySemiconvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_chart_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ K>0,∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ p∈Kp,∀ u : M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ConvexOn ℝ (ball (extChartAt 𝓘(ℝ,Model n) a a) r)
        (fun z => Φ (p,cTransform u ((extChartAt 𝓘(ℝ,Model n) a).symm z))+K/2*‖z‖^2) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨K0,hK0,r0,hr0,hr0T,hSup⟩ := uniform_cTransform_chart_lower (n := n) a
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨L,r1,hr1,hr1T,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  obtain ⟨K,hK,H⟩ := scalar_family_uniform_semiconvex (E := Model n) hΦ hKp hmono A B K0 hK0.le (D*L)
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  have hsub0 : ball (χ a) r⊆ball (χ a) r0 := ball_subset_ball (min_le_left _ _)
  have hsub1 : ball (χ a) r⊆ball (χ a) r1 := ball_subset_ball (min_le_right _ _)
  refine ⟨K,hK,r,hr,fun z hz => hr0T (hsub0 hz),?_⟩
  intro p hp u hu hb
  apply H p hp _ (convex_ball _ _) _
  · exact (cTransform_lipschitz hu (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))).comp_lipschitzOnWith (hL.mono hsub1)
  · exact fun z hz => hb _
  · intro z hz
    obtain ⟨l,hl⟩ := hSup u hu z (hsub0 hz)
    exact ⟨l,fun y hy => hl y (hsub0 hy)⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_MaximumScalarJets
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

attribute [local instance] OAI.WeakMTWTransport.maximumScalarDualGroup
attribute [local instance] OAI.WeakMTWTransport.maximumScalarDualSpace
local instance maximumScalarBilinearGroup_rc61819_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumScalarBilinearSpace_rc61819_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma MaximumDiagonal.scalar_jets_oai
    {u v:M → ℝ} (hu:Continuous u) {Lv:ℝ≥0} (hv:LipschitzWith Lv v)
    (hdual:IsCostDualPair u v) {α D bminus bplus A₀ B₀:ℝ} {Bc Bo:ℝ → ℝ}
    {ho:Continuous Bo} (hBc:ContDiff ℝ ∞ Bc)
    (hmono:∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (hrange:∀y,v y∈Icc A₀ B₀)
    (hslope:∀b∈Icc bminus bplus,∀y:M,
      0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1)
    {hmtw:WeakMTW (n:=n) (M:=M)}
    {F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo} {a c:M} {N:Set (Model n)}
    {J:MaximumJensenFamily hmtw hv.continuous ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {Q:M → Prop} {r:ℝ} (hr:0 < r)
    (hgood:∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r,z∉N →
      Q ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {g:Model n →L[ℝ] ℝ} {H:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hg:Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g))
    (hH:Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H)) :
    ∃p:ℕ → Model n,∃A:ℕ → Model n →L[ℝ] Model n,
      (∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) ∧
        (∀d e,inner ℝ (A k d) e=inner ℝ d (A k e)) ∧
        HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
          v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (p k) (A k)) ∧
      Tendsto (fun k=>innerSL ℝ (p k)) atTop (𝓝 g) ∧
      Tendsto (fun k=>(innerSL ℝ).comp (A k)) atTop (𝓝 H) := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  let i:=fun k=>J.sampleIndex k (S.ν k)
  let φ:=fun k s=>modifiedScalar α D Bc (F.b k,s)
  have hφ (k:ℕ):ContDiff ℝ ∞ (φ k):=
    (modifiedScalar_contDiff hBc α D).comp (contDiff_const.prodMk contDiff_id)
  have hsl (k:ℕ) (y:M):0<deriv (φ k) (v y) ∧ deriv (φ k) (v y)<1:=
    hslope _ (Ioo_subset_Icc_self (F.parameter k)) y
  have hHn : Tendsto (fun k => ‖fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))‖) atTop (𝓝 ‖H‖) := hH.norm
  have HG:∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (i k)) d d≤(‖H‖+1)*‖d‖^2:=by
    filter_upwards [hHn.eventually (gt_mem_nhds (show ‖H‖<‖H‖+1 by linarith))] with k hk
    intro d
    exact (le_abs_self _).trans ((bilinear_quadratic_norm_bound _ d).trans
      (mul_le_mul_of_nonneg_right hk.le (sq_nonneg _)))
  have Hgood:=S.good_centers hBc.continuous hx hz HG
  have HE:∀ᶠ k in atTop,Q ((J.sample k).Y ((J.sample k).z (i k))) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
      (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
      HasQuadraticExpansion (fun h=>v (χ.symm (J.sampleCenter k (S.ν k)+h))) p A:=by
    filter_upwards [Hgood,hx.eventually (ball_mem_nhds _ hr)] with k hk hb
    have HH:=hgood _ hb hk
    have hY:χ.symm (J.sampleCenter k (S.ν k))=(J.sample k).Y ((J.sample k).z (i k)):=
      χ.left_inv ((J.sample k).samples (i k)).1
    rw [hY] at HH
    exact HH
  obtain ⟨K,hK,R,hR,hRT,Hsem⟩:=uniform_family_chart_semiconvex (n:=n)
    (modifiedScalar_contDiff hBc α D) isCompact_Icc hmono A₀ B₀ c
  have HB:∀y,cTransform u y∈Icc A₀ B₀:=by rwa [←hdual.2]
  have HS:∀ᶠ k in atTop,∃r>0,∃K:ℝ,
      ConvexOn ℝ (ball (J.sampleCenter k (S.ν k)) r)
      (fun q=>φ k (v (χ.symm q))+K/2*‖q‖^2):=by
    filter_upwards [hx.eventually (ball_mem_nhds _ (half_pos hR))] with k hk
    have hs:=Hsem (F.b k) (Ioo_subset_Icc_self (F.parameter k)) u hu HB
    rw [←hdual.2] at hs
    refine ⟨R/2,half_pos hR,K,hs.subset ?_ (convex_ball _ _)⟩
    intro z hz'
    change dist z (χ c)<R
    calc
      dist z (χ c) ≤ dist z (J.sampleCenter k (S.ν k))+dist (J.sampleCenter k (S.ν k)) (χ c):=dist_triangle _ _ _
      _ < R/2+R/2:=add_lt_add hz' hk
      _ = R:=by ring
  obtain ⟨p,A,HPA,HA,_⟩:=hmtw.jensen_undo_short hu hv hdual hφ hsl
    (fun k=>(F.prefixTime k).1) (fun k=>(F.prefixTime k).2) J.sample i F.time hz hg hH
    (HE.mono (fun k hk=>hk.2)) HS
  have hgrad:∀ᶠ k in atTop,(coordinatePhaseFlow c (1-F.t k,(J.sample k).z (i k),
      fderiv ℝ (chartCenterEnvelope (fun y=>φ k (v y)) (F.t k) c) ((J.sample k).z (i k)))).2=
      innerSL ℝ (p k):=by
    filter_upwards [HS,HPA] with k Hs Hp
    obtain ⟨r,hr,K,Hs⟩:=Hs
    exact hmtw.jensen_phase_gradient hu hv hdual (hφ k) (hsl k)
      (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (i k)
      (S.chart k) hr Hp.1 Hp.2 Hs
  exact ⟨p,A,(HE.and HPA).mono (fun k hk=>⟨hk.1.1,hk.2⟩),
    phase_gradient_tendsto F.time hz hg hgrad,HA⟩
end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets_oai.{u_1} := @OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets_oai.{u_1}
