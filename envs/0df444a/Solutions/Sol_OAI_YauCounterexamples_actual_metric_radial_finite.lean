-- Prove2me | solution 1 for OAI.YauCounterexamples.actual_metric_radial_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:58:50.968157+00:00
-- url     : https://prove2.me/submissions/3a87f17c-d515-4d4c-a9de-c2ef592d4627

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_actual_radialCorrugation_strict_shift
import Theorems.Thm_OAI_YauCounterexamples_exists_local_metric_radial_patch

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialLeadingTrace
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in

lemma exists_unit_common_kernel (hd : 3 ≤ Module.finrank ℝ E)
    (R T : E →L[ℝ] ℝ) : ∃ w : E, ‖w‖ = 1 ∧ R w = 0 ∧ T w = 0 := by
  classical
  let L : E →ₗ[ℝ] ℝ × ℝ := R.toLinearMap.prod T.toLinearMap
  have hn : ¬Function.Injective L := by
    intro h
    have hh := LinearMap.finrank_le_finrank_of_injective h
    have ht : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    rw [ht] at hh
    omega
  unfold Function.Injective at hn
  push Not at hn
  obtain ⟨v,z,he,hne⟩ := hn
  have hvz : v-z ≠ 0 := sub_ne_zero.mpr hne
  have hl : L (v-z) = 0 := by rw [map_sub,he,sub_self]
  have hR : R (v-z) = 0 := congrArg Prod.fst hl
  have hT : T (v-z) = 0 := congrArg Prod.snd hl
  refine ⟨‖v-z‖⁻¹ • (v-z),?_,?_,?_⟩
  · simp [norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvz)]
  · simp only [map_smul,hR,smul_zero]
  · simp only [map_smul,hT,smul_zero]

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ProfileTraceAdd
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_norm_gain {a d : E} (had : inner ℝ a d = 0) (q : ℝ) :
    ‖a + q • d‖^2 = ‖a‖^2 + q^2 * ‖d‖^2 := by
  rw [norm_add_sq_real]
  simp [inner_smul_right,had,norm_smul, mul_pow]

theorem radial_gradient_no_loss (a r e : E) (had : inner ℝ a r = 0)
    (q ε : ℝ) (he : ‖e‖ ≤ ε*‖a‖) :
    (1-ε)*‖a‖ ≤ ‖a+q • r+e‖ := by
  have hsq := radial_norm_gain had q
  have hnorm : ‖a‖ ≤ ‖a+q • r‖ := by
    nlinarith [norm_nonneg a,norm_nonneg (a+q • r),mul_nonneg (sq_nonneg q) (sq_nonneg ‖r‖)]
  have htri : ‖a+q • r‖ ≤ ‖a+q • r+e‖+‖e‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+q • r+e) e
  linarith

theorem radial_gradient_annular_gain (a r e : E) (had : inner ℝ a r = 0)
    (δ A f c ε : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hf : c ≤ f)
    (hA : ‖a‖/2 ≤ A) (hr : (1:ℝ)/2 ≤ ‖r‖) (he : ‖e‖ ≤ ε*‖a‖) :
    (Real.sqrt (1+δ^2*c^2/16)-ε)*‖a‖ ≤ ‖a+(δ*A*f) • r+e‖ := by
  have hA0 : 0 ≤ A := (div_nonneg (norm_nonneg a) (by norm_num)).trans hA
  have hq : δ*‖a‖*c/2 ≤ δ*A*f := by
    have h1 := mul_le_mul_of_nonneg_right hA hc
    have h2 := mul_le_mul_of_nonneg_left hf hA0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ
    nlinarith only [h3]
  have hq0 : 0 ≤ δ*‖a‖*c/2 := by positivity
  have hq2 := (sq_le_sq₀ hq0 (hq0.trans hq)).mpr hq
  have hr2 : (1:ℝ)/4 ≤ ‖r‖^2 := by nlinarith
  have hp := mul_le_mul hq2 hr2 (by norm_num : (0:ℝ) ≤ 1/4) (sq_nonneg (δ*A*f))
  have hs := radial_norm_gain had (δ*A*f)
  have hroot : (Real.sqrt (1+δ^2*c^2/16))^2 = 1+δ^2*c^2/16 :=
    Real.sq_sqrt (by positivity)
  have hsq : (Real.sqrt (1+δ^2*c^2/16)*‖a‖)^2 ≤ ‖a+(δ*A*f) • r‖^2 := by
    rw [mul_pow,hroot]
    nlinarith only [hp,hs]
  have hnorm := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (1+δ^2*c^2/16)*‖a‖)
    (norm_nonneg (a+(δ*A*f) • r))).mp hsq
  have htri : ‖a+(δ*A*f) • r‖ ≤ ‖a+(δ*A*f) • r+e‖+‖e‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+(δ*A*f) • r+e) e
  linarith


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff

lemma profileLattice_embedding : IsClosedEmbedding profileLatticePoint :=
  Int.isClosedEmbedding_coe_real.prodMap Int.isClosedEmbedding_coe_real

theorem profile_translates_locallyFinite (f : ProfilePlane → ℝ) (hf : HasCompactSupport f) :
    LocallyFinite (fun k : ProfileLattice => support (fun x => f (x-profileLatticePoint k))) := by
  obtain ⟨R,hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ProfilePlane)
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  have hfin : (profileLatticePoint ⁻¹' closedBall (0 : ProfilePlane) (‖x‖+1+R)).Finite :=
    (profileLattice_embedding.isCompact_preimage (isCompact_closedBall _ _)).finite_of_discrete
  apply hfin.subset
  rintro k ⟨y,hy,hyx⟩
  have hr : ‖y-profileLatticePoint k‖ ≤ R := by
    simpa only [mem_closedBall,dist_zero_right] using hR (subset_closure hy)
  have hyb : ‖y‖ < ‖x‖+1 := by
    have hh : ‖y‖ ≤ ‖y-x‖ + ‖x‖ := by
      calc
        ‖y‖ = ‖(y-x)+x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
    rw [mem_ball,dist_eq_norm] at hyx
    linarith
  simp only [mem_preimage,mem_closedBall,dist_zero_right]

  calc
    ‖profileLatticePoint k‖ = ‖y-(y-profileLatticePoint k)‖ := by congr 1; abel
    _ ≤ ‖y‖ + ‖y-profileLatticePoint k‖ := norm_sub_le _ _
    _ ≤ ‖x‖+1+R := by linarith

theorem profilePeriodize_smooth (f : ProfilePlane → ℝ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (profilePeriodize f) := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun k => contMDiff_iff_contDiff.mpr
    (hs.comp (contDiff_id.sub contDiff_const))) (profile_translates_locallyFinite f hf)


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma radialPrimitive_hasDeriv (β : ℝ → ℝ) (hβ : Continuous β) (s : ℝ) :
    HasDerivAt (radialPrimitive β) (β s) s :=
  (hβ.integral_hasStrictDerivAt 0 s).hasDerivAt

lemma radialPrimitive_smooth (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (radialPrimitive β) := by
  rw [contDiff_infty_iff_deriv]
  have hd : deriv (radialPrimitive β) = β := funext fun s => (radialPrimitive_hasDeriv β hβ.continuous s).deriv
  refine ⟨fun s => (radialPrimitive_hasDeriv β hβ.continuous s).differentiableAt, ?_⟩
  rw [hd]
  exact hβ

lemma radialPrimitive_constant {β : ℝ → ℝ} (hβ : Continuous β) {b s : ℝ}
    (hzero : ∀ t, b ≤ t → β t = 0) (hs : b ≤ s) :
    radialPrimitive β s = radialPrimitive β b := by
  have hI : ∫ t in b..s, β t = 0 := by
    calc
      _ = ∫ _ in b..s, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc b s := by simpa only [uIcc_of_le hs] using ht
        exact hzero t ht'.1
      _ = 0 := intervalIntegral.integral_zero
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hβ.intervalIntegrable 0 b) (hβ.intervalIntegrable b s)
  simpa only [radialPrimitive,hI,add_zero] using hh.symm

lemma radialSquaredBase_smooth (β : ℝ → ℝ) (b : ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (radialSquaredBase β b) :=
  ((radialPrimitive_smooth β hβ).comp
    ((contDiff_fst.pow 2).add (contDiff_snd.pow 2))).sub contDiff_const

lemma radialSquaredBase_zero {β : ℝ → ℝ} (hβ : Continuous β) {b : ℝ}
    (hzero : ∀ t, b ≤ t → β t = 0) (x : ProfilePlane) (hx : b ≤ x.1^2+x.2^2) :
    radialSquaredBase β b x = 0 := by
  simp [radialSquaredBase,radialPrimitive_constant hβ hzero hx]

lemma radialSquaredBase_compact {β : ℝ → ℝ} (hβ : Continuous β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    HasCompactSupport (radialSquaredBase β b) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ProfilePlane) R)
  intro x hx
  apply radialSquaredBase_zero hβ hzero x
  have hxn : R < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  rw [Prod.norm_def,lt_max_iff] at hxn
  rcases hxn with hx | hx
  · rw [Real.norm_eq_abs] at hx
    have hsq : R^2 < x.1^2 := by nlinarith [sq_abs x.1]
    nlinarith [sq_nonneg x.2]
  · rw [Real.norm_eq_abs] at hx
    have hsq : R^2 < x.2^2 := by nlinarith [sq_abs x.2]
    nlinarith [sq_nonneg x.1]

theorem radial_periodic_smooth {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    ContDiff ℝ ∞ (fun x : ProfilePlane => radialPrimitive β b +
      profilePeriodize (radialSquaredBase β b) x) := by
  exact contDiff_const.add (profilePeriodize_smooth _
    (radialSquaredBase_compact hβ.continuous hR hb hzero) (radialSquaredBase_smooth β b hβ))


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped ContDiff

lemma profileRadiusSquared_hasFDeriv (x : ProfilePlane) :
    HasFDerivAt (fun z : ProfilePlane => z.1^2+z.2^2)
      ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  convert ((hasFDerivAt_fst (𝕜:=ℝ) (p:=x)).pow 2).add
    ((hasFDerivAt_snd (𝕜:=ℝ) (p:=x)).pow 2) using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | simp

theorem radialSquaredBase_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (b : ℝ) (x v : ProfilePlane) :
    fderiv ℝ (radialSquaredBase β b) x v =
      2*β (x.1^2+x.2^2)*(x.1*v.1+x.2*v.2) := by
  have hh := ((radialPrimitive_hasDeriv β hβ.continuous (x.1^2+x.2^2)).comp_hasFDerivAt x
    (profileRadiusSquared_hasFDeriv x)).sub_const (radialPrimitive β b)
  change HasFDerivAt (radialSquaredBase β b) _ x at hh
  rw [hh.fderiv]
  simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profilePeriodize_eventually_zero {f : ProfilePlane → ℝ} {r R : ℝ}
    (hrR : r < R) (hf : ∀ z, r < ‖z‖ → f z = 0) (x : ProfilePlane)
    (hx : ∀ k, R ≤ ‖x-profileLatticePoint k‖) :
    profilePeriodize f =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrR)] with z hz
  have hd : ‖z-x‖ < R-r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hz0 : ∀ k, f (z-profileLatticePoint k) = 0 := by
    intro k
    apply hf
    have ht : ‖x-profileLatticePoint k‖ ≤ ‖z-x‖+‖z-profileLatticePoint k‖ := by
      calc
        _ = ‖(x-z)+(z-profileLatticePoint k)‖ := by congr 1; abel
        _ ≤ ‖x-z‖+‖z-profileLatticePoint k‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev x z]
    linarith only [ht,hd,hx k]
  simp [profilePeriodize,hz0]

lemma profilePeriodize_jets_zero {f : ProfilePlane → ℝ} {r R : ℝ}
    (hrR : r < R) (hf : ∀ z, r < ‖z‖ → f z = 0) (x : ProfilePlane)
    (hx : ∀ k, R ≤ ‖x-profileLatticePoint k‖) :
    fderiv ℝ (profilePeriodize f) x = 0 ∧
    fderiv ℝ (fderiv ℝ (profilePeriodize f)) x = 0 := by
  have he := profilePeriodize_eventually_zero hrR hf x hx
  constructor
  · simpa using he.fderiv_eq (𝕜 := ℝ)
  · simpa using (he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

lemma plane_radius_pos {z : ProfilePlane} (hz : z ≠ 0) :
    0 < Real.sqrt (z.1^2+z.2^2) := by
  apply Real.sqrt_pos.mpr
  have hp : 0 ≤ z.1^2+z.2^2 := by positivity
  apply lt_of_le_of_ne hp
  intro he
  apply hz
  ext <;> simp only [Prod.fst_zero,Prod.snd_zero]
  · nlinarith only [sq_nonneg z.2,he]
  · nlinarith only [sq_nonneg z.1,he]

lemma plane_radial_angular_sq (z v : ProfilePlane) :
    (planeRadialCovector z v)^2+(planeAngularCovector z v)^2 = v.1^2+v.2^2 := by
  by_cases hz : z = 0
  · simp [planeRadialCovector,planeAngularCovector,hz]
  · have hs := plane_radius_pos hz
    have hs2 := Real.sq_sqrt (show 0 ≤ z.1^2+z.2^2 by positivity)
    simp only [planeRadialCovector,planeAngularCovector,ite_eq_right hz,
      _root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp
    rw [hs2]
    ring

lemma radialSquaredBase_radial_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (b : ℝ) (z v : ProfilePlane) :
    fderiv ℝ (radialSquaredBase β b) z v =
      (2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2))*planeRadialCovector z v := by
  rw [radialSquaredBase_first hβ]
  by_cases hz : z = 0
  · simp [hz,hβ0]
  · have hs := plane_radius_pos hz
    simp only [planeRadialCovector,ite_eq_right hz,_root_.add_apply,
      _root_.smul_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ProfilePeriodizeFirst
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

theorem profilePeriodize_single {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (k : ProfileLattice) {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ ≤ R) :
    profilePeriodize f x = f (x-profileLatticePoint k) := by
  unfold profilePeriodize
  apply finsum_eq_single
  intro l hl
  apply hf
  have hsep := profileLattice_separated hl
  have htri : ‖profileLatticePoint l-profileLatticePoint k‖ ≤
      ‖x-profileLatticePoint l‖+‖x-profileLatticePoint k‖ := by
    calc
      _ = ‖(profileLatticePoint l-x)+(x-profileLatticePoint k)‖ := by congr 1; abel
      _ ≤ ‖profileLatticePoint l-x‖+‖x-profileLatticePoint k‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (profileLatticePoint l) x]
  linarith

theorem profilePeriodize_eventually_single {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (k : ProfileLattice) {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ < R) :
    profilePeriodize f =ᶠ[𝓝 x] (fun z => f (z-profileLatticePoint k)) := by
  have ho : IsOpen {z : ProfilePlane | ‖z-profileLatticePoint k‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [ho.mem_nhds hx] with z hz
  exact profilePeriodize_single hR hf k (le_of_lt hz)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profilePeriodize_first {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (hs : Differentiable ℝ f) (k : ProfileLattice) {x : ProfilePlane}
    (hx : ‖x-profileLatticePoint k‖ < R) (v : ProfilePlane) :
    fderiv ℝ (profilePeriodize f) x v = fderiv ℝ f (x-profileLatticePoint k) v := by
  rw [(profilePeriodize_eventually_single hR hf k hx).fderiv_eq]
  have hh := (hs (x-profileLatticePoint k)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (profileLatticePoint k))
  erw [hh.fderiv]
  simp



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialSpeedPositiveAnnulus
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma radialSquaredBase_zero_of_norm {β : ℝ → ℝ} (hβ : Continuous β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x : ProfilePlane) (hx : R < ‖x‖) : radialSquaredBase β b x = 0 := by
  apply radialSquaredBase_zero hβ hzero
  rw [Prod.norm_def,lt_max_iff] at hx
  rcases hx with hx | hx
  · rw [Real.norm_eq_abs] at hx
    have hh : R^2 < x.1^2 := by nlinarith [sq_abs x.1]
    nlinarith [sq_nonneg x.2]
  · rw [Real.norm_eq_abs] at hx
    have hh : R^2 < x.2^2 := by nlinarith [sq_abs x.2]
    nlinarith [sq_nonneg x.1]


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

theorem periodicRadialFunction_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hsmall : 2*R < 1) (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x v : ProfilePlane) :
    fderiv ℝ (periodicRadialFunction β b) x v =
      periodicRadialSpeed β R x * planeRadialCovector (periodicRadialOffset R x) v := by
  unfold periodicRadialFunction
  simp only [fderiv_const_add]
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hR : 0 ≤ R := hr.trans hrR.le
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 :=
    fun z hz => hf z (hrR.trans hz)
  by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
  · simp only [periodicRadialSpeed,periodicRadialOffset,dite_eq_left hx]
    rw [profilePeriodize_first hsmall hfR
      ((radialSquaredBase_smooth β b hβ).differentiable (by simp)) hx.choose hx.choose_spec]
    exact radialSquaredBase_radial_first hβ hβ0 b _ v
  · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
    have hz := (profilePeriodize_jets_zero hrR hf x hxn).1
    simp [periodicRadialSpeed,periodicRadialOffset,hx,hz]


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma metricProfileTraceForm_apply (B H : CoordinateForm E) (a v : E) :
    metricProfileTraceForm B H a v v = B v v*H a a+(1+B a a)*H v v := by
  simp only [metricProfileTraceForm,add_apply,smul_apply,smul_eq_mul]
  ring

attribute [local instance] OAI.YauCounterexamples.dualNorm
attribute [local instance] OAI.YauCounterexamples.dualSpace
theorem compact_quadraticPlaneFull_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (T : X → CoordinateForm E) (q : X → E)
    (hT : Continuous T) (hq : Continuous q)
    (hfull : ∀ x ∈ K, quadraticPlaneFull (T x) (q x)) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v, inner ℝ (q x) v = 0 →
      m*‖v‖^2 ≤ T x v v := by
  let S : Set (X × E) := {p | p.1 ∈ K ∧ ‖p.2‖ = 1 ∧ inner ℝ (q p.1) p.2 = 0}
  have hS : IsCompact S := by
    have heq : S = (K ×ˢ sphere (0 : E) 1) ∩ {p | inner ℝ (q p.1) p.2 = 0} := by
      ext p
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_sphere_zero_iff_norm]
      tauto
    rw [heq]
    exact (hK.prod (isCompact_sphere 0 1)).inter_right
      (isClosed_eq ((hq.comp continuous_fst).inner continuous_snd) continuous_const)
  have hc : Continuous (fun p : X × E => T p.1 p.2 p.2) :=
    ((hT.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v, ‖v‖ = 1 →
      inner ℝ (q x) v = 0 → m ≤ T x v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
      exact ⟨T p.1 p.2 p.2,hfull p.1 hp.1 p.2 hp.2.1 hp.2.2,
        fun x hx v hv hav => hmin (show (x,v) ∈ S from ⟨hx,hv,hav⟩)⟩
    · exact ⟨1,zero_lt_one,fun x hx v hv hav => (hne ⟨(x,v),hx,hv,hav⟩).elim⟩
  obtain ⟨m,hm,hml⟩ := hm
  refine ⟨m,hm,?_⟩
  intro x hx v hav
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hqw : inner ℝ (q x) w = 0 := by simp [w,inner_smul_right,hav]
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : T x v v = ‖v‖^2 * T x w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq,mul_comm m]
  exact mul_le_mul_of_nonneg_left (hml x hx w hw hqw) (sq_nonneg _)

theorem compact_variableMetric_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (B T : X → CoordinateForm E) (q : X → E)
    (hB : Continuous B) (hT : Continuous T) (hq : Continuous q)
    (hfull : ∀ x ∈ K, quadraticPlaneFull (T x) (q x)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, ∀ v,
      B x v v = 1 → inner ℝ (q x) v = 0 → m ≤ T x v v := by
  obtain ⟨m,hm,hml⟩ := compact_quadraticPlaneFull_margin hK T q hT hq hfull
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hB.continuousOn
  let C' := max C 1
  have hCp : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min (m/C') 1,lt_min (div_pos hm hCp) zero_lt_one,min_le_right _ _,?_⟩
  intro x hx v hv hav
  have hbound : 1 ≤ C'*‖v‖^2 := by
    calc
      1 = |B x v v| := by rw [hv,abs_one]
      _ ≤ ‖B x‖*‖v‖*‖v‖ := (B x).le_opNorm₂ v v
      _ ≤ C'*‖v‖^2 := by
        have hh := mul_le_mul_of_nonneg_right ((hC x hx).trans (le_max_left C 1)) (sq_nonneg ‖v‖)
        nlinarith only [hh]
  calc
    min (m/C') 1 ≤ m/C' := min_le_left _ _
    _ ≤ m*‖v‖^2 := (div_le_iff₀ hCp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hbound hm.le])
    _ ≤ T x v v := hml x hx v hav

omit [FiniteDimensional ℝ E] in
lemma twoCoframeForm_apply (D : E →L[ℝ] (ℝ × ℝ)) (v : E) :
    twoCoframeForm D v v = (D v).1^2+(D v).2^2 := by
  change (D v).1*(D v).1+(D v).2*(D v).2 = _
  ring

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

lemma metricGradient_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g u x) =
      (selfMetricFlat g x).inverse (fderiv ℝ u x) := by
  symm
  apply (selfMetricFlat_invertible g x).inverse_apply_eq.mpr
  ext v
  have h := (metricGradient_pairing g u x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)).symm
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ u x v = g.inner x (metricGradient g u x) ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v) at h
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using h

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)

theorem compact_metric_tangent_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ J : ℝ, 0 < J ∧ ∀ x ∈ K, ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap‖ ≤ J := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹,inv_pos.mpr (Real.sqrt_pos.mpr hm),?_⟩
  intro x hx
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml x hx ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
  have hnorm : selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
      ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
    have hn := real_inner_self_eq_norm_sq (v : TangentSpace 𝓘(ℝ,E) x)
    change g.inner x v v = ‖v‖^2 at hn
    simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn
  rw [hnorm] at hlow
  have hh : Real.sqrt m * ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  change ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v‖ ≤ (Real.sqrt m)⁻¹ * ‖v‖
  rw [←div_eq_inv_mul,le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance genericHessMapNorm_ra27a3f_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_ra27a3f_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_ra27a3f_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_iff_nonzero (T : CoordinateForm E) (q : E) :
    quadraticPlaneStrict T q ↔ ∃ v, v ≠ 0 ∧ inner ℝ q v = 0 ∧ 0 < T v v := by
  constructor
  · rintro ⟨v,hv,hq,hp⟩
    exact ⟨v,norm_ne_zero_iff.mp (by rw [hv]; norm_num),hq,hp⟩
  · rintro ⟨v,hv,hq,hp⟩
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v,?_,?_,?_⟩
    · simp [norm_smul,ne_of_gt hn]
    · simp [inner_smul_right,hq]
    · simpa only [map_smul,smul_apply,smul_eq_mul] using
        mul_pos (inv_pos.mpr hn) (mul_pos (inv_pos.mpr hn) hp)

lemma coordinateMetricGradient_eq (g : SmoothMetric E E) (ψ : E → ℝ) (x : E) :
    coordinateMetricGradient g ψ x =
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) x) (metricGradient g ψ x) :=
  (metricGradient_self g ψ x).symm

attribute [local instance] OAI.YauCounterexamples.actualDualNorm
attribute [local instance] OAI.YauCounterexamples.actualDualSpace
lemma contDiff_coordinateMetricGradient (g : SmoothMetric E E) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (coordinateMetricGradient g ψ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  exact hGi.clm_apply (hψ.fderiv_right (m:=∞) (by simp))

lemma continuous_actualProfileTraceForm (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileTraceForm g u) :=
  by
    have hB : Continuous (selfMetricFlat g) := (contDiff_selfMetricFlat g).continuous
    have hH : Continuous (actualCoordinateHessian g u) :=
      continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu
    have ha : Continuous (coordinateMetricGradient g u) :=
      (contDiff_coordinateMetricGradient g hu).continuous
    change Continuous (fun x => metricProfileTraceForm (selfMetricFlat g x)
      (actualCoordinateHessian g u x) (coordinateMetricGradient g u x))
    unfold metricProfileTraceForm
    exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
      ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_metric_norm (g : SmoothMetric E E) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v : TangentSpace 𝓘(ℝ,E) x,
      selfMetricFlat g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v)
        ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = ‖v‖^2 := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro v
  have hn := real_inner_self_eq_norm_sq v
  change g.inner x v v = ‖v‖^2 at hn
  simpa only [selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hn

lemma actualProfileTraceForm_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    let H := (actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
    ∀ v : TangentSpace 𝓘(ℝ,E) x, actualProfileTraceForm g u x (j v) (j v) =
      ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
        (1+‖metricGradient g u x‖^2)*H v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j H v
  rw [actualProfileTraceForm,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
  rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
  rfl

omit [FiniteDimensional ℝ E] in
lemma profileStrict_iff_quadratic (H : ProfileForm E) (a : E) :
    profileStrict H a ↔ quadraticPlaneStrict (metricProfileTraceForm (innerSL ℝ) H a) a := by
  have ht (v : E) (hv : ‖v‖ = 1) :
      metricProfileTraceForm (innerSL ℝ) H a v v = profileTrace H a v := by
    rw [metricProfileTraceForm_apply]
    change inner ℝ v v * H a a + (1+inner ℝ a a)*H v v = profileTrace H a v
    simp only [real_inner_self_eq_norm_sq,hv,one_pow,one_mul,profileTrace]
  constructor
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv]⟩
  · rintro ⟨v,hv,hav,hp⟩
    exact ⟨v,hv,hav,by rwa [ht v hv] at hp⟩

omit [FiniteDimensional ℝ E] in
lemma quadraticPlaneStrict_transport {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (j : V ≃L[ℝ] E) (T : CoordinateForm E) (S : CoordinateForm V)
    (q : E) (a : V) (hT : ∀ v, T (j v) (j v) = S v v)
    (hq : ∀ v, inner ℝ q (j v) = inner ℝ a v) :
    quadraticPlaneStrict T q ↔ quadraticPlaneStrict S a := by
  rw [quadraticPlaneStrict_iff_nonzero,quadraticPlaneStrict_iff_nonzero]
  constructor
  · rintro ⟨v,hv,hqv,hp⟩
    refine ⟨j.symm v,by simpa using hv,?_,?_⟩
    · rw [←hq,j.apply_symm_apply]
      exact hqv
    · rwa [←hT,j.apply_symm_apply]
  · rintro ⟨v,hv,hqv,hp⟩
    exact ⟨j v,by simpa using hv,(hq v).trans hqv,by rwa [hT]⟩

lemma coordinateProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (H₀ : CoordinateForm E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    quadraticPlaneStrict (metricProfileTraceForm (selfMetricFlat g x) H₀ (coordinateMetricGradient g u x))
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) ↔ profileStrict
      (H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  intro j
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) := Module.Finite.equiv j.symm.toLinearEquiv
  let H := H₀.bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap
  rw [profileStrict_iff_quadratic]
  apply quadraticPlaneStrict_transport j
  · intro v
    rw [metricProfileTraceForm_apply,metricProfileTraceForm_apply,coordinateMetricGradient_eq]
    rw [selfMetricFlat_metric_norm,selfMetricFlat_metric_norm]
    change ‖v‖^2*H (metricGradient g u x) (metricGradient g u x) +
      (1+‖metricGradient g u x‖^2)*H v v =
      inner ℝ v v*H (metricGradient g u x) (metricGradient g u x) +
      (1+inner ℝ (metricGradient g u x) (metricGradient g u x))*H v v
    simp only [real_inner_self_eq_norm_sq]
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    change fderiv ℝ u x (j v) = g.inner x (metricGradient g u x) v
    rw [metricGradient_pairing,mfderiv_eq_fderiv]
    rfl

lemma actualProfileStrict_iff_tangent (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
    actualProfileStrict g u x ↔ profileStrict
      ((actualCoordinateHessian g u x).bilinearComp j.toContinuousLinearMap j.toContinuousLinearMap)
      (metricGradient g u x) :=
  coordinateProfileStrict_iff_tangent g u x (actualCoordinateHessian g u x)


end

section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem corrugation_first {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v : E) :
    fderiv ℝ (fun z => ψ z+c*χ z*F (N • y z)) x v =
      fderiv ℝ ψ x v + c*fderiv ℝ χ x v*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v) := by
  have dhψ := hψ.differentiable (by simp) x
  have dhχ := hχ.differentiable (by simp) x
  have dhy := hy.differentiable (by simp) x
  have dhF := hF.differentiable (by simp) (N • y x)
  have dhny := dhy.const_smul N
  have dhcomp := dhF.comp x dhny
  erw [fderiv_fun_add dhψ ((dhχ.const_mul c).mul dhcomp),
    fderiv_fun_mul (dhχ.const_mul c) dhcomp,
    fderiv_const_mul dhχ c, fderiv_fun_comp x dhF dhny,
    fderiv_fun_const_smul dhy N]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_smul,smul_eq_mul,Function.comp_apply,Pi.smul_apply]
  ring


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

theorem periodicRadialFunction_bounded {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, |periodicRadialFunction β b x| ≤ B := by
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 := fun z hz => hf z (hrR.trans hz)
  obtain ⟨B,hB⟩ := ((radialSquaredBase_compact hβ.continuous hr hb hzero).isCompact_range
    (radialSquaredBase_smooth β b hβ).continuous).exists_bound_of_continuousOn
    (f := id) continuous_id.continuousOn
  refine ⟨|radialPrimitive β b|+max B 0+1,by positivity,?_⟩
  intro x
  have hp : |profilePeriodize (radialSquaredBase β b) x| ≤ max B 0 := by
    by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
    · rw [(profilePeriodize_eventually_single hsmall hfR hx.choose hx.choose_spec).eq_of_nhds]
      exact (hB _ (mem_range_self _)).trans (le_max_left _ _)
    · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
      rw [(profilePeriodize_eventually_zero hrR hf x hxn).eq_of_nhds]
      simp
  unfold periodicRadialFunction
  calc
    _ ≤ |radialPrimitive β b|+|profilePeriodize (radialSquaredBase β b) x| := abs_add_le _ _
    _ ≤ |radialPrimitive β b|+max B 0+1 := by linarith only [hp]


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
lemma pulledGradient_pairing (j : V →L[ℝ] E) (u : E → ℝ) (x : E) (v : V) :
    inner ℝ (pulledGradient j u x) v = fderiv ℝ u x (j v) :=
  InnerProductSpace.toDual_symm_apply

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma norm_bilinear_pullback_le (H : ProfileForm E) (j : V →L[ℝ] E) :
    ‖H.bilinearComp j j‖ ≤ ‖H‖*‖j‖^2 := by
  apply (H.bilinearComp j j).opNorm_le_bound₂ (by positivity)
  intro v w
  calc
    ‖H (j v) (j w)‖ ≤ ‖H‖*‖j v‖*‖j w‖ := H.le_opNorm₂ _ _
    _ ≤ ‖H‖*(‖j‖*‖v‖)*(‖j‖*‖w‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (j.le_opNorm v) (norm_nonneg H))
        (j.le_opNorm w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma planeRadialCovector_le_radius (z v : ProfilePlane) :
    |planeRadialCovector z v| ≤ Real.sqrt (v.1^2+v.2^2) := by
  have he := plane_radial_angular_sq z v
  have hs := Real.sq_sqrt (show 0 ≤ v.1^2+v.2^2 by positivity)
  have ha := sq_abs (planeRadialCovector z v)
  nlinarith only [he,hs,ha,sq_nonneg (planeAngularCovector z v),
    abs_nonneg (planeRadialCovector z v),Real.sqrt_nonneg (v.1^2+v.2^2)]

lemma radial_coframe_bounds (D : V →L[ℝ] ProfilePlane) (a : V) (z : ProfilePlane)
    (ha : D a = 0)
    (hup : ∀ v, Real.sqrt ((D v).1^2+(D v).2^2) ≤ 2*‖v‖)
    (hlo : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((D v).1^2+(D v).2^2)) :
    let R := (planeRadialCovector z).comp D
    let T := (planeAngularCovector z).comp D
    R a = 0 ∧ T a = 0 ∧ ‖(InnerProductSpace.toDual ℝ V).symm R‖ ≤ 2 ∧
      ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2) := by
  dsimp only
  refine ⟨by simp [ha],by simp [ha],?_,?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (planeRadialCovector_le_radius z (D v)).trans (hup v)
  · intro v hv
    simpa only [ContinuousLinearMap.comp_apply,plane_radial_angular_sq] using hlo v hv

omit [FiniteDimensional ℝ E] in
lemma radialCorrugation_smooth {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b r R : ℝ} (hr : 0 ≤ r)
    (_hrR : r < R) (_hsmall : 2*R < 1) (hb : b ≤ r^2)
    (hzero : ∀ t, b ≤ t → β t = 0) (δ A N : ℝ) :
    ContDiff ℝ ∞ (radialCorrugation ψ χ y β b δ A N) := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) := by
    exact radial_periodic_smooth hβ hr hb hzero
  exact hψ.add (contDiff_const.mul (hχ.mul (hF.comp (hy.const_smul N))))

omit [FiniteDimensional ℝ E] in
lemma radialCorrugation_gradient {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (j : V →L[ℝ] E) (δ A N : ℝ) (hN : N ≠ 0) (x : E) :
    pulledGradient j (radialCorrugation ψ χ y β b δ A N) x =
      pulledGradient j ψ x +
        (δ*A*χ x*periodicRadialSpeed β R (N • y x)) •
          (InnerProductSpace.toDual ℝ V).symm
            ((planeRadialCovector (periodicRadialOffset R (N • y x))).comp ((fderiv ℝ y x).comp j)) +
        (δ*A/N*periodicRadialFunction β b (N • y x)) • pulledGradient j χ x := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) :=
    radial_periodic_smooth hβ hr hb hzero
  apply ext_inner_right ℝ
  intro v
  rw [pulledGradient_pairing,inner_add_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    pulledGradient_pairing,pulledGradient_pairing,InnerProductSpace.toDual_symm_apply]
  have he := corrugation_first hψ hχ hF hy (δ*A/N) N x (j v)
  have heq : (fun z => ψ z+(δ*A/N)*χ z*periodicRadialFunction β b (N • y z)) =
      radialCorrugation ψ χ y β b δ A N := by funext z; dsimp [radialCorrugation]; ring
  rw [heq,periodicRadialFunction_first hβ hβ0 hr hrR hsmall hb hzero] at he
  simp only [ContinuousLinearMap.comp_apply]
  rw [he]
  field_simp [hN]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PulledGradientNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
lemma pulledGradient_norm_le (j : V →L[ℝ] E) (u : E → ℝ) (x : E) :
    ‖pulledGradient j u x‖ ≤ ‖fderiv ℝ u x‖*‖j‖ := by
  rw [pulledGradient,LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_comp_le _ _



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ActualRadialCorrugationStrictShift
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coframe_radial_norm_lower (hd : 3 ≤ Module.finrank ℝ E)
    (a : E) (R T : E →L[ℝ] ℝ)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2)) :
    (1:ℝ)/2 ≤ ‖(InnerProductSpace.toDual ℝ E).symm R‖ := by
  obtain ⟨v,hv,hav,hTv⟩ := exists_unit_common_kernel hd (InnerProductSpace.toDual ℝ E a) T
  have hh := hco v hav
  rw [hv,hTv,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] at hh
  have hi := abs_real_inner_le_norm ((InnerProductSpace.toDual ℝ E).symm R) v
  rw [InnerProductSpace.toDual_symm_apply,hv,mul_one] at hi
  exact hh.trans hi

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialCorrugation_support (ψ χ : E → ℝ) (y : E → ProfilePlane)
    (β : ℝ → ℝ) (b δ A N : ℝ) :
    tsupport (fun x => radialCorrugation ψ χ y β b δ A N x-ψ x) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp [radialCorrugation,hx]

end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem actual_radialCorrugation_gain_shift
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (α δ A c ε : ℝ) (hα : 0 < α) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hε : 0 < ε) (hε1 : ε < 1)
    (ha : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (hA : ∀ x, ‖pulledGradient (j x) ψ x‖/2 ≤ A)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
      pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x ≠ 0 ∧
      (1-ε)*‖pulledGradient (j x) ψ x‖ ≤
        ‖pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x‖ ∧
      (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y x+d)) →
        (Real.sqrt (1+δ^2*c^2/16)-ε)*‖pulledGradient (j x) ψ x‖ ≤
          ‖pulledGradient (j x) (radialCorrugation ψ χ (fun t => y t+d) β b δ A N) x‖) := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let C := |δ*A| * B*(max D 0)*J
  have hn : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds (mul_pos hε hα)),eventually_gt_atTop (0:ℕ)] with N hCN hN d x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let a := pulledGradient (j x) ψ x
  let z := periodicRadialOffset R ((N:ℝ) • (y x+d))
  let D₁ := (fderiv ℝ y x).comp (j x)
  let R₁ := (planeRadialCovector z).comp D₁
  let T₁ := (planeAngularCovector z).comp D₁
  let r₁ := (InnerProductSpace.toDual ℝ (V x)).symm R₁
  let e := (δ*A/(N:ℝ)*periodicRadialFunction β b ((N:ℝ) • (y x+d))) • pulledGradient (j x) χ x
  let f := periodicRadialSpeed β R ((N:ℝ) • (y x+d))
  have hframes := radial_coframe_bounds D₁ a z (hfirst x) (hup x) (hlo x)
  have har : inner ℝ a r₁ = 0 := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply.trans hframes.1
  have hre : (1:ℝ)/2 ≤ ‖r₁‖ := coframe_radial_norm_lower (hd x) a R₁ T₁ hframes.2.2.2
  have heg : ‖pulledGradient (j x) χ x‖ ≤ max D 0*J :=
    (pulledGradient_norm_le (j x) χ x).trans <|
      (mul_le_mul_of_nonneg_left (hj x) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right ((hD x x.property).trans (le_max_left _ _)) hJ)
  have heC : ‖e‖ ≤ C/(N:ℝ) := by
    dsimp only [e,C]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hNp]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B)*(max D 0*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hNp.le)) heg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have he : ‖e‖ ≤ ε*‖a‖ := heC.trans (hCN.le.trans (mul_le_mul_of_nonneg_left (ha x) hε.le))
  have heq := radialCorrugation_gradient hψ hχ (hy.add (contDiff_const (c:=d))) hβ hβ0 hr hrR hsmall hb hz (j x) δ A N hNp.ne' x
  simp only [fderiv_add_const] at heq
  rw [heq]
  change a+(δ*A*χ x*f) • r₁+e ≠ 0 ∧ _
  have hnl := radial_gradient_no_loss a r₁ e har (δ*A*χ x*f) ε he
  refine ⟨norm_pos_iff.mp ((mul_pos (sub_pos.mpr hε1) (hα.trans_le (ha x))).trans_le hnl),hnl,?_⟩
  intro hχx hfx
  rw [hχx,mul_one]
  exact radial_gradient_annular_gain a r₁ e har δ A f c ε hδ hc hfx (hA x) hre he

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialCorrugation_uniform_C0_shift {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0) (δ A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x, |radialCorrugation ψ χ (fun t => y t+d) β b δ A N x-ψ x| < ε := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hz
  have hn : Tendsto (fun N : ℕ => |δ*A| * B/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hn.eventually (Iio_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with N hNε hN d x
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hχb : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχ x).1]; exact (hχ x).2
  have ht : |χ x*periodicRadialFunction β b ((N:ℝ) • (y x+d))| ≤ B := by
    rw [abs_mul]
    calc
      _ ≤ 1*B := mul_le_mul hχb (hBF _) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  dsimp only [radialCorrugation]
  rw [add_sub_cancel_left,abs_mul,abs_div,abs_of_pos hNp]
  exact (mul_le_mul_of_nonneg_left ht (div_nonneg (abs_nonneg _) hNp.le)).trans_lt
    (by simpa only [div_mul_eq_mul_div] using hNε)

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_eq (g : SmoothMetric E E) (x v : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    actualCoordinateNorm g x v = ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  have he := selfMetricFlat_metric_norm g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at he
  rw [actualCoordinateNorm,he,Real.sqrt_sq (norm_nonneg _)]

lemma actualProfileSpeed_eq (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    actualProfileSpeed g u x = ‖metricGradient g u x‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [actualProfileSpeed,actualCoordinateNorm_eq,coordinateMetricGradient_eq,
    ContinuousLinearEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_nonneg (g : SmoothMetric E E) (x v : E) :
    0 ≤ actualCoordinateNorm g x v := Real.sqrt_nonneg _

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < actualCoordinateNorm g x v := Real.sqrt_pos.mpr (selfMetricFlat_pos g x hv)

attribute [local instance] OAI.YauCounterexamples.globalPrepDualNorm
attribute [local instance] OAI.YauCounterexamples.globalPrepDualSpace
local instance globalPrepInvNorm_ra27a3f_1 : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance globalPrepInvSpace_ra27a3f_1 : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma continuous_actualCoordinateNorm (g : SmoothMetric E E) {v : E → E}
    (hv : Continuous v) : Continuous (fun x => actualCoordinateNorm g x (v x)) :=
  (((contDiff_selfMetricFlat g).continuous.clm_apply hv).clm_apply hv).sqrt

lemma continuous_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileSpeed g u) :=
  continuous_actualCoordinateNorm g (contDiff_coordinateMetricGradient g hu).continuous

lemma compact_actual_speed_pos (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (ha : ∀ x ∈ K, coordinateMetricGradient g u x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ actualProfileSpeed g u x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne (continuous_actualProfileSpeed g hu).continuousOn
    exact ⟨_,actualCoordinateNorm_pos g x (ha x hx),hm⟩
  · exact ⟨1,zero_lt_one,fun x hx => (hne ⟨x,hx⟩).elim⟩

lemma actualJet_eventuallyEq (g : SmoothMetric E E) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) :
    coordinateMetricGradient g u x = coordinateMetricGradient g v x ∧
    actualCoordinateHessian g u x = actualCoordinateHessian g v x ∧
    (actualProfileStrict g u x ↔ actualProfileStrict g v x) ∧
    (actualProfileFull g u x ↔ actualProfileFull g v x) := by
  have h₁ := h.fderiv_eq (𝕜:=ℝ)
  have h₂ := (h.fderiv (𝕜:=ℝ)).fderiv_eq (𝕜:=ℝ)
  have hg : coordinateMetricGradient g u x = coordinateMetricGradient g v x := by
    simp only [coordinateMetricGradient,h₁]
  have hh : actualCoordinateHessian g u x = actualCoordinateHessian g v x := by
    simp only [actualCoordinateHessian,coordinateCovariantSecond,h₁,h₂]
  exact ⟨hg,hh,by simp only [actualProfileStrict,actualProfileTraceForm,hg,hh,h₁],
    by simp only [actualProfileFull,actualProfileTraceForm,hg,hh,h₁]⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma disjoint_sum_eventuallyEq {ι : Type*} [Fintype ι]
    (u : E → ℝ) (f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (f i))) (x : E) :
    ((fun y => u y+∑ i, f i y) =ᶠ[𝓝 x] u) ∨
      ∃ i, x ∈ tsupport (f i) ∧
        (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  by_cases hx : ∃ i, x ∈ tsupport (f i)
  · obtain ⟨i,hi⟩ := hx
    right
    refine ⟨i,hi,?_⟩
    have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
      · exact (notMem_tsupport_iff_eventuallyEq.mp ((hd hji).notMem_of_mem_right hi)).mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]
  · left
    have hz : ∀ i, ∀ᶠ y in 𝓝 x, f i y = 0 := fun i =>
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx ⟨i,hh⟩)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    simp only [hy,Finset.sum_const_zero,add_zero]

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PreparationWaveSecondGtOne
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ENNReal NNReal Topology
namespace YauCounterexamples
variable {X G : Type*} [MeasurableSpace X] [MeasurableSpace G]
  [AddGroup G] [MeasurableAdd₂ G]
  (μ : Measure X) [SFinite μ] (ν : Measure G) [SFinite ν]
  [ν.IsAddLeftInvariant]

theorem periodic_phase_average (a : X → G) (ha : Measurable a)
    {E : Set G} (hE : MeasurableSet E) :
    (∫⁻ τ, μ {x | a x + τ ∈ E} ∂ν) = μ univ * ν E := by
  have hh : Measurable (fun p : X × G => E.indicator (fun _ => (1 : ℝ≥0∞)) (a p.1+p.2)) :=
    (measurable_const.indicator hE).comp ((ha.comp measurable_fst).add measurable_snd)
  have hleft (τ : G) : (∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ) =
      μ {x | a x+τ ∈ E} := by
    rw [show (fun x => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun x => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext x; rfl]
    rw [lintegral_indicator (hE.preimage (ha.add_const τ)), lintegral_one, Measure.restrict_apply_univ]
    rfl
  have hright (x : X) : (∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν) = ν E := by
    rw [show (fun τ => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun τ => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext τ; rfl]
    have hm : Measurable (fun τ : G => a x + τ) := measurable_const.add measurable_id
    rw [lintegral_indicator (hE.preimage hm), lintegral_one, Measure.restrict_apply_univ]
    exact measure_preimage_add ν (a x) E
  calc
    _ = ∫⁻ τ, ∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ ∂ν := by simp_rw [hleft]
    _ = ∫⁻ x, ∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν ∂μ :=
      (lintegral_lintegral_swap hh.aemeasurable).symm
    _ = _ := by simp [hright,mul_comm]

theorem exists_periodic_phase_mass [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (a : X → G) (ha : Measurable a) {E : Set G} (hE : MeasurableSet E) :
    ∃ τ : G, μ univ * ν E ≤ μ {x | a x+τ ∈ E} := by
  have hi := periodic_phase_average μ ν a ha hE
  obtain ⟨τ,hτ⟩ := exists_lintegral_le (μ:=ν)
    (f:=fun τ => μ {x | a x+τ ∈ E}) (by rw [hi]; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  exact ⟨τ,hi ▸ hτ⟩
end YauCounterexamples

end


end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactDisjointSmoothCutoffs
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
open Set Filter Function Metric Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem compact_disjoint_smooth_cutoffs (K V : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K))
    (hV : ∀ i, IsOpen (V i)) (hKV : ∀ i, K i ⊆ V i) :
    ∃ χ : ι → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        tsupport (χ i) ⊆ V i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ i x = 1) ∧
        ∀ x, χ i x ∈ Icc 0 1) ∧ Pairwise (Disjoint on fun i => tsupport (χ i)) := by
  have hN : Pairwise (Disjoint on fun i => 𝓝ˢ (K i)) := by
    intro i j hij
    change Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))
    rw [(hK i).disjoint_nhdsSet_left]
    intro x hx
    rw [(hK j).disjoint_nhdsSet_right]
    intro y hy
    exact disjoint_nhds_nhds.mpr (fun hxy => (hd hij).notMem_of_mem_left hx (hxy ▸ hy))
  obtain ⟨O,hO,hdO⟩ := hN.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  have hex (i : ι) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ V i ∩ O i ∧ (∀ᶠ x in 𝓝ˢ (K i), χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
    obtain ⟨B,hB,hKB,hBc⟩ := exists_isOpen_superset_and_isCompact_closure (hK i)
    have hNV : V i ∩ O i ∩ B ∈ 𝓝ˢ (K i) :=
      ((hV i).inter (hO i).1 |>.inter hB).mem_nhdsSet.mpr
        (fun x hx => ⟨⟨hKV i hx,(hO i).2 hx⟩,hKB hx⟩)
    obtain ⟨W,hW,hKW,hWsub⟩ := (hK i).exists_isOpen_closure_subset hNV
    obtain ⟨f,hf1,hf0,hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ,E)) (n := ⊤) (hK i).isClosed (t := W) (by simpa only [hW.interior_eq] using hKW)
    have hfs : tsupport (f : E → ℝ) ⊆ closure W := by
      apply closure_mono
      intro x hx
      by_contra hh
      exact hx (hf0 x hh)
    refine ⟨f,contMDiff_iff_contDiff.mp f.contMDiff,?_,?_,hf1,hf⟩
    · exact hBc.of_isClosed_subset (isClosed_tsupport _)
        (hfs.trans (hWsub.trans (fun x hx => subset_closure hx.2)))
    · exact hfs.trans (hWsub.trans (fun x hx => hx.1))
  choose χ hχ using hex
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_left,
    (hχ i).2.2.2.1,(hχ i).2.2.2.2⟩,?_⟩
  intro i j hij
  exact (hdO hij).mono ((hχ i).2.2.1.trans inter_subset_right)
    ((hχ j).2.2.1.trans inter_subset_right)
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_FinitePrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_disjoint_profile_cores (μ : Measure E) [SFinite μ]
    {U : Set E} (hU : IsOpen U) (V : E → Set E) (hV : ∀ x ∈ U, V x ∈ 𝓝 x)
    {a : ℝ≥0∞} (ha : a < μ U) :
    ∃ (t : Finset E) (r : E → ℝ),
      (∀ x ∈ t, x ∈ U ∧ 0 < r x ∧ closedBall x (r x) ⊆ U ∩ V x) ∧
      (t : Set E).PairwiseDisjoint (fun x => closedBall x (r x)) ∧
      a < μ (⋃ x ∈ t, closedBall x (r x)) := by
  classical
  let f : E → Set ℝ := fun x => {r | closedBall x r ⊆ U ∩ V x}
  have hf : ∀ x ∈ U, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    have hn : U ∩ V x ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) (hV x hx)
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨min r δ / 2, ⟨?_, by constructor <;> nlinarith [lt_min hr hδ, min_le_right r δ]⟩⟩
    exact (closedBall_subset_ball (by nlinarith [lt_min hr hδ, min_le_left r δ])).trans hrsub
  obtain ⟨s,r,hs,hsU,hr,hcover,hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae μ f U hf (fun _ => 1) (by intro x hx; norm_num)
  have hμ : μ (⋃ x ∈ s, closedBall x (r x)) = μ U := by
    apply le_antisymm (measure_mono ?_)
    · exact measure_mono_ae (ae_le_set.mpr hcover)
    · intro y hy
      obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
      exact (hr x hx).1 hy |>.1
  let : Countable s := hs.to_subtype
  let A : Finset s → Set E := fun t => ⋃ x ∈ t, closedBall (x : E) (r x)
  have hmono : Monotone A := by
    intro t v htv y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x,htv hx,hy⟩
  have hUnion : (⋃ t : Finset s, A t) = ⋃ x ∈ s, closedBall x (r x) := by
    ext y
    simp only [A, mem_iUnion]
    constructor
    · rintro ⟨t,x,hx,hy⟩
      exact ⟨x,x.property,hy⟩
    · rintro ⟨x,hx,hy⟩
      exact ⟨{⟨x,hx⟩},⟨x,hx⟩,Finset.mem_singleton_self _,hy⟩
  have hsup : a < ⨆ t : Finset s, μ (A t) := by
    rw [← hmono.measure_iUnion, hUnion, hμ]
    exact ha
  obtain ⟨t,ht⟩ := lt_iSup_iff.mp hsup
  refine ⟨t.image Subtype.val,r,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hsU y.property,(hr y y.property).2.1,(hr y y.property).1⟩
  · intro x hx y hy hxy
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    exact hdisj x'.property y'.property hxy
  · simpa [A] using ht
end YauCounterexamples

end

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma disjoint_supported_sum_eq_patch {ι : Type*} [Fintype ι]
    (u : E → ℝ) (χ f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (χ i)))
    (hf : ∀ i, tsupport (f i) ⊆ tsupport (χ i)) {i : ι} {x : E}
    (hx : x ∈ tsupport (χ i)) :
    (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
    · exact (notMem_tsupport_iff_eventuallyEq.mp
        (fun hh => (hd hji).notMem_of_mem_right hx (hf j hh))).mono (fun _ hh _ => hh)
  filter_upwards [Filter.eventually_all.mpr hz] with y hy
  rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RadialMetricDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma pulledGradient_metric (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
      Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toLinearEquiv
    pulledGradient (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap u x =
      metricGradient g u x := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toLinearEquiv
  apply (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).injective
  ext v
  rw [InnerProductSpace.toDual_apply_apply,pulledGradient_pairing]
  change fderiv ℝ u x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = g.inner x (metricGradient g u x) v
  rw [metricGradient_pairing,mfderiv_eq_fderiv]
  rfl

local instance radialMetricDualNorm_ra27a3f_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialMetricDualSpace_ra27a3f_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
lemma compact_actual_full_margin (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (hfull : ∀ x ∈ K, actualProfileFull g u x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ,E) x,
      ‖v‖ = 1 → inner ℝ (metricGradient g u x) v = 0 →
      m ≤ profileTrace (pulledHessian (metricChristoffel g)
        (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap u x) (metricGradient g u x) v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  obtain ⟨m,hm,hm1,hml⟩ := compact_variableMetric_margin hK (selfMetricFlat g)
    (actualProfileTraceForm g u) q (contDiff_selfMetricFlat g).continuous
    (continuous_actualProfileTraceForm g hu)
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp (hu.continuous_fderiv (by simp))) hfull
  refine ⟨m,hm,hm1,?_⟩
  intro x hx v hv hav
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
  have hB : selfMetricFlat g x (j v) (j v) = 1 := by
    rw [selfMetricFlat_metric_norm,hv,one_pow]
  have hq : inner ℝ (q x) (j v) = 0 := by
    rw [InnerProductSpace.toDual_symm_apply]
    have he := metricGradient_pairing g u x v
    rw [mfderiv_eq_fderiv] at he
    exact he.symm.trans hav
  have hh := hml x hx (j v) hB hq
  rw [actualProfileTraceForm_tangent,hv,one_pow,one_mul] at hh
  exact hh

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.radialShiftMetricDualNorm
attribute [local instance] OAI.YauCounterexamples.radialShiftMetricDualSpace
theorem actual_metric_radial_patch_shift (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {K₀ : Set E} (hK₀ : IsCompact K₀)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (ha : ∀ x ∈ K₀, coordinateMetricGradient g ψ x ≠ 0)
    (hfull : ∀ x ∈ K₀, actualProfileFull g ψ x)
    (hfirst : ∀ x ∈ K₀, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0)
    (hup : ∀ x ∈ K₀, ∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v)
    (hlo : ∀ x ∈ K₀, ∀ v, fderiv ℝ ψ x v = 0 →
      selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
    {b r R δ A c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (hδ : 0 < δ) (hA : 0 < A) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
    (hAa : ∀ x ∈ K₀, A ≤ 2*actualProfileSpeed g ψ x)
    (haA : ∀ x ∈ K₀, actualProfileSpeed g ψ x/2 ≤ A)
    (Fmax S K : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hK : 0 < K)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      0 ≤ periodicAngularSecond β R z ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ K)
    (hsmall : 9216*K*S*δ^2 ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, let v := radialCorrugation ψ χ (fun t => y t+d) β b δ A N
      ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-ψ x) ∧
      tsupport (fun x => v x-ψ x) ⊆ tsupport χ ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      ∀ x ∈ K₀, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x ∧
        (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y x+d)) →
          (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let V : K₀ → Type _ := fun x => TangentSpace 𝓘(ℝ,E) (x:E)
  let : ∀ x : K₀, NormedAddCommGroup (V x) := fun x => inferInstanceAs (NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) (x:E)))
  let : ∀ x : K₀, InnerProductSpace ℝ (V x) := fun x => inferInstanceAs (InnerProductSpace ℝ (TangentSpace 𝓘(ℝ,E) (x:E)))
  let j : ∀ x : K₀, V x →L[ℝ] E := fun x => (NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).toContinuousLinearMap
  let : ∀ x : K₀, FiniteDimensional ℝ (V x) := fun x =>
    Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).symm.toLinearEquiv
  have hd : ∀ x : K₀, 3 ≤ Module.finrank ℝ (V x) := fun x => by
    rw [(NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).toLinearEquiv.finrank_eq,hdim]
  obtain ⟨J,hJ,hj⟩ := compact_metric_tangent_bound g hK₀
  obtain ⟨α,hα,hαa⟩ := compact_actual_speed_pos g hψ hK₀ ha
  obtain ⟨M,hMa⟩ := hK₀.exists_bound_of_continuousOn (f:=actualProfileSpeed g ψ)
    (continuous_actualProfileSpeed g hψ).continuousOn
  obtain ⟨H,hH⟩ := hK₀.exists_bound_of_continuousOn (f:=actualCoordinateHessian g ψ)
    (continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hψ).continuousOn
  obtain ⟨m,hm,hm1,hmargin⟩ := compact_actual_full_margin g hψ hK₀ hfull
  have hgr (x : K₀) : ‖pulledGradient (j x) ψ x‖ = actualProfileSpeed g ψ x := by
    rw [actualProfileSpeed_eq,pulledGradient_metric]
  have hhh (x : K₀) : ‖pulledHessian (metricChristoffel g) (j x) ψ x‖ ≤ |H| *J^2 := by
    exact (norm_bilinear_pullback_le _ _).trans (mul_le_mul
      ((hH x x.property).trans (le_abs_self H)) (sq_le_sq₀ (norm_nonneg _) hJ.le |>.mpr (hj x x.property))
      (sq_nonneg _) (abs_nonneg _))
  have hf (x : K₀) : fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0 := by
    rw [pulledGradient_metric]
    change fderiv ℝ y x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)) (metricGradient g ψ x)) = 0
    rw [←coordinateMetricGradient_eq]
    exact hfirst x x.property
  have hU (x : K₀) (v : V x) :
      Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖ := by
    have hh := hup x x.property (j x v)
    dsimp only [j, ContinuousLinearEquiv.coe_coe] at hh
    rw [selfMetricFlat_metric_norm,twoCoframeForm_apply] at hh
    change (fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2 ≤ 4*‖v‖^2 at hh
    exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
  have hL (x : K₀) (v : V x) (hv : inner ℝ (pulledGradient (j x) ψ x) v = 0) :
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) := by
    have hh := hlo x x.property (j x v) ((pulledGradient_pairing _ _ _ _).symm.trans hv)
    dsimp only [j, ContinuousLinearEquiv.coe_coe] at hh
    rw [selfMetricFlat_metric_norm,twoCoframeForm_apply] at hh
    change ‖v‖^2 ≤ 4*((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) at hh
    have hs := Real.sq_sqrt (show 0 ≤ (fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2 by positivity)
    nlinarith [Real.sqrt_nonneg ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2),norm_nonneg v]
  have hs := actual_radialCorrugation_strict_shift K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
    (metricChristoffel g) (contDiff_metricChristoffel g).continuous hψ hχ hy hχs hχv hβ hβ0 hβv
    hr hrR hR hb hz Fmax K S hFmax.le hK.le hS.le
    (fun z => ⟨(hcoef z).1,(hcoef z).2.1,(hcoef z).2.2.2⟩)
    m α (|M|) (|H| *J^2) δ A hm hm1 hα (abs_nonneg _) (by positivity) hδ hA
    hsmall
    (fun x => by rw [hgr]; exact hαa x x.property)
    (fun x => by rw [hgr]; exact (le_abs_self _).trans ((hMa x x.property).trans (le_abs_self M))) hhh
    (fun x => by rw [hgr]; exact hAa x x.property)
    (fun x v hv hav => by rw [pulledGradient_metric] at hav ⊢; exact hmargin x x.property v hv hav)
    hf hU hL
  have hg := actual_radialCorrugation_gain_shift K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
    hψ hχ hy hβ hβ0 hr hrR hR hb hz α δ A c ε hα hδ.le hc hε hε1
    (fun x => by rw [hgr]; exact hαa x x.property)
    (fun x => by rw [hgr]; exact haA x x.property) hf hU hL
  have h₀ := radialCorrugation_uniform_C0_shift (ψ:=ψ) (y:=y) hχv hβ hr hrR hR hb hz δ A hε₀
  filter_upwards [hs,hg,h₀] with N hs hg h₀ d
  let v := radialCorrugation ψ χ (fun t => y t+d) β b δ A N
  have hsup := radialCorrugation_support (ψ:=ψ) (χ:=χ) (y:=fun t => y t+d) (β:=β) b δ A (N:ℝ)
  refine ⟨radialCorrugation_smooth hψ hχ (hy.add contDiff_const) hβ hr hrR hR hb hz δ A N,?_,hsup,h₀ d,?_⟩
  · exact hχs.of_isClosed_subset isClosed_closure hsup
  · intro x hx
    let x₀ : K₀ := ⟨x,hx⟩
    have hss := hs d x₀
    have hgg := hg d x₀
    rw [pulledGradient_metric] at hss hgg
    rw [pulledGradient_metric] at hgg
    refine ⟨?_,(actualProfileStrict_iff_tangent g v x).mpr hss.1,?_,?_⟩
    · rw [coordinateMetricGradient_eq]
      exact fun hh => hss.2 ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).injective (hh.trans (map_zero _).symm))
    · simpa only [actualProfileSpeed_eq] using hgg.2.1
    · simpa only [actualProfileSpeed_eq] using hgg.2.2
end


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

lemma profileTorusQuotient_lift (τ : ProfileTorus) :
    profileTorusQuotient (profileTorusLift τ) = τ := by
  simp [profileTorusQuotient,profileTorusLift]

end


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma profileTorusQuotient_add (z w : ProfilePlane) :
    profileTorusQuotient (z+w) = profileTorusQuotient z+profileTorusQuotient w := rfl

lemma continuous_profileTorusQuotient : Continuous profileTorusQuotient :=
  ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)

lemma radial_phase_fraction (q : ProfilePlane) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/4) :
    ((volume : Measure UnitAddCircle).prod volume)
      (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) =
      ENNReal.ofReal ((2*ρ)^2) := by
  rw [Measure.prod_prod]
  have hb (x : UnitAddCircle) : volume (ball x ρ) = ENNReal.ofReal (2*ρ) := by
    rw [←measure_congr (AddCircle.closedBall_ae_eq_ball (x:=x) (ε:=ρ)),
      AddCircle.volume_closedBall,min_eq_right (by linarith : 2*ρ ≤ 1)]
  rw [hb,hb,pow_two]
  exact (ENNReal.ofReal_mul (show 0 ≤ 2*ρ by positivity)).symm

theorem exists_radial_phase {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (y : X → ProfilePlane) (hy : Measurable y)
    (N : ℝ) (q : ProfilePlane) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/4) :
    ∃ τ : ProfilePlane, μ univ * ENNReal.ofReal ((2*ρ)^2) ≤
      μ {x | profileTorusQuotient (N • y x+τ) ∈
        ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ} := by
  let ν : Measure ProfileTorus := (volume : Measure UnitAddCircle).prod volume
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have ha : Measurable (fun x => profileTorusQuotient (N • y x)) :=
    continuous_profileTorusQuotient.measurable.comp (hy.const_smul N)
  obtain ⟨τ,hτ⟩ := exists_periodic_phase_mass μ ν
    (fun x => profileTorusQuotient (N • y x)) ha
    (E:=ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ)
    (measurableSet_ball.prod measurableSet_ball)
  refine ⟨profileTorusLift τ,?_⟩
  simp_rw [profileTorusQuotient_add,profileTorusQuotient_lift]
  rw [show ν (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) =
    ENNReal.ofReal ((2*ρ)^2) from radial_phase_fraction q hρ hρ1] at hτ
  exact hτ

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_eventuallyEq (g : SmoothMetric E E) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : actualProfileSpeed g u x = actualProfileSpeed g v x := by
  rw [actualProfileSpeed,actualProfileSpeed,(actualJet_eventuallyEq g h).1]

theorem actual_metric_radial_finite_oai (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {Ω U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g ψ x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g ψ x)
    (hfull : ∀ x ∈ U, actualProfileFull g ψ x)
    (μ : Measure E) [IsFiniteMeasure μ]
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
    {b r R δ c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
    (Fmax S Kb : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hKb : 0 < Kb)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      0 ≤ periodicAngularSecond β R z ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ Kb)
    (hsmall : 9216*Kb*S*δ^2 ≤ 1)
    (q : ProfilePlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hwindow : ∀ z, profileTorusQuotient z ∈
      ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
        c ≤ periodicRadialSpeed β R z) :
    ∃ (v : E → ℝ) (G : Set E), ContDiff ℝ ∞ v ∧
      HasCompactSupport (fun x => v x-ψ x) ∧ tsupport (fun x => v x-ψ x) ⊆ U ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) ∧
      MeasurableSet G ∧ G ⊆ U ∧
      μ U/2 * ENNReal.ofReal ((2*ρ)^2) ≤ μ G ∧
      ∀ x ∈ G, (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
        actualProfileSpeed g v x := by
  classical
  by_cases hzero : μ U = 0
  · refine ⟨ψ,∅,hψ,?_,?_,?_,?_,MeasurableSet.empty,empty_subset _,?_,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · simpa using (fun _ : E => hε₀)
    · intro x hx
      refine ⟨ha x hx,hstrict x hx,?_⟩
      have hn := actualCoordinateNorm_nonneg g x (coordinateMetricGradient g ψ x)
      change 0 ≤ actualProfileSpeed g ψ x at hn
      nlinarith
    · simp [hzero]
    · simp
  have hhalf : μ U/2 < μ U := by
    have hh := ENNReal.mul_lt_mul_left hzero (measure_ne_top μ U)
      (by norm_num : (1/2 : ℝ≥0∞) < 1)
    simpa only [one_mul,div_eq_mul_inv,one_mul,mul_comm] using hh
  have hloc : ∀ p : E, ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧
      (p ∈ U → p ∈ W ∧ ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
        fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
        (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
        (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
        A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A) := by
    intro p
    by_cases hp : p ∈ U
    · obtain ⟨W,y,A,hWo,hWp,hy,hA,hd⟩ := exists_local_metric_radial_patch hdim g hψ
        (ha p (subset_closure (hUΩ hp)))
      exact ⟨W,y,A,hWo,fun _ => ⟨hWp,hy,hA,hd⟩⟩
    · exact ⟨∅,0,1,isOpen_empty,fun h => (hp h).elim⟩
  choose W y A hWo hW using hloc
  obtain ⟨t,r₀,ht,htd,htm⟩ := finite_disjoint_profile_cores μ hU W
    (fun p hp => (hWo p).mem_nhds (hW p hp).1) hhalf
  let ι := {p // p ∈ t}
  let C : ι → Set E := fun i => closedBall i.val (r₀ i.val)
  have hC : ∀ i, IsCompact (C i) := fun _ => isCompact_closedBall _ _
  have hCd : Pairwise (Disjoint on C) := by
    intro i j hij
    exact htd i.property j.property (fun he => hij (Subtype.ext he))
  obtain ⟨χ,hχ,hχd⟩ := compact_disjoint_smooth_cutoffs C (fun i => U ∩ W i.val) hC hCd
    (fun i => hU.inter (hWo i.val)) (fun i => (ht i.val i.property).2.2)
  have hχ1 : ∀ i, ∀ x ∈ C i, χ i x = 1 := fun i x hx =>
    (eventually_nhdsSet_iff_forall.mp (hχ i).2.2.2.1 x hx).self_of_nhds
  have hCχ : ∀ i, C i ⊆ tsupport (χ i) := by
    intro i x hx
    apply subset_tsupport
    simp only [Function.mem_support,hχ1 i x hx,ne_eq,one_ne_zero,not_false_eq_true]
  let w (i : ι) (N : ℕ) (d : ProfilePlane) :=
    radialCorrugation ψ (χ i) (fun x => y i.val x+d) β b δ (A i.val) N
  have hpdata : ∀ i : ι, ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane,
      ContDiff ℝ ∞ (w i N d) ∧ HasCompactSupport (fun x => w i N d x-ψ x) ∧
      tsupport (fun x => w i N d x-ψ x) ⊆ tsupport (χ i) ∧
      (∀ x, |w i N d x-ψ x| < ε₀) ∧
      ∀ x ∈ tsupport (χ i), coordinateMetricGradient g (w i N d) x ≠ 0 ∧
        actualProfileStrict g (w i N d) x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g (w i N d) x ∧
        (χ i x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y i.val x+d)) →
          (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
            actualProfileSpeed g (w i N d) x) := by
    intro i
    have hi := hW i.val (ht i.val i.property).1
    have hreg := fun x hx => (hχ i).2.2.1 (show x ∈ tsupport (χ i) from hx)
    exact actual_metric_radial_patch_shift hdim g (hχ i).2.1 hψ (hχ i).1 hi.2.1
      (hχ i).2.1 (hχ i).2.2.2.2
      (fun x hx => ha x (subset_closure (hUΩ (hreg x hx).1)))
      (fun x hx => hfull x (hreg x hx).1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.1)
      hβ hβ0 hβv hr hrR hR hb hz hδ hi.2.2.1 hc hε hε1 hε₀
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.2.1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.2.2)
      Fmax S Kb hFmax hS hKb hcoef hsmall
  obtain ⟨N,hNpos,hN⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (Filter.eventually_all.mpr hpdata)).exists
  have hNz : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  let D : Set E := ⋃ i, C i
  have hDm : MeasurableSet D := MeasurableSet.iUnion fun i => (hC i).measurableSet
  have hDU : D ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ((ht i.val i.property).2.2 hi).1
  have hMD : μ U/2 ≤ μ D := by
    apply le_of_lt
    convert htm using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp only [D,C,ι,mem_iUnion,Subtype.exists,exists_prop]
  let yg : E → ProfilePlane := fun x => ∑ i, (C i).indicator (y i.val) x
  have hyg : Measurable yg := Finset.measurable_sum _ (fun i _ =>
    ((hW i.val (ht i.val i.property).1).2.1.continuous.measurable).indicator (hC i).measurableSet)
  have hygi : ∀ i, ∀ x ∈ C i, yg x = y i.val x := by
    intro i x hx
    dsimp only [yg]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hx _
    · intro j _ hji
      exact indicator_of_notMem ((hCd hji).notMem_of_mem_right hx) _
    · simp
  obtain ⟨τ,hτ⟩ := exists_radial_phase (μ.restrict D) yg hyg (N:ℝ) q hρ.le hρ1
  let d : ProfilePlane := (N:ℝ)⁻¹ • τ
  have hphase (x : E) (i : ι) (hx : x ∈ C i) :
      (N:ℝ) • (y i.val x+d) = (N:ℝ) • yg x+τ := by
    rw [hygi i x hx,smul_add,show (N:ℝ) • d = τ by dsimp [d]; rw [smul_smul,mul_inv_cancel₀ hNz,one_smul]]
  let f : ι → E → ℝ := fun i x => w i N d x-ψ x
  let v : E → ℝ := fun x => ψ x+∑ i, f i x
  have hv : ContDiff ℝ ∞ v := hψ.add (ContDiff.sum (fun i _ => (hN i d).1.sub hψ))
  have hfs : ∀ i, tsupport (f i) ⊆ tsupport (χ i) := fun i => (hN i d).2.2.1
  have hfd : Pairwise (Disjoint on fun i => tsupport (f i)) := fun i j hij =>
    (hχd hij).mono (hfs i) (hfs j)
  have heq : ∀ i, ∀ x ∈ tsupport (χ i), v =ᶠ[𝓝 x] w i N d := by
    intro i x hx
    simpa only [f,add_sub_cancel] using disjoint_supported_sum_eq_patch ψ χ f hχd hfs hx
  have hcases (x : E) : (v =ᶠ[𝓝 x] ψ) ∨ ∃ i, x ∈ tsupport (χ i) ∧ v =ᶠ[𝓝 x] w i N d := by
    rcases disjoint_sum_eventuallyEq ψ f hfd x with h|⟨i,hi,hei⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,hfs i hi,heq i x (hfs i hi)⟩
  have hvs : tsupport (fun x => v x-ψ x) ⊆ ⋃ i, tsupport (χ i) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    by_contra hh
    have hz : ∀ i, f i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hh (mem_iUnion_of_mem i (hfs i hi)))
    exact hx (by simp [v,hz])
  have hcpt : HasCompactSupport (fun x => v x-ψ x) :=
    (isCompact_iUnion fun i => (hχ i).2.1).of_isClosed_subset (isClosed_tsupport _) hvs
  have hsub : tsupport (fun x => v x-ψ x) ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hvs hx)
    exact ((hχ i).2.2.1 hi).1
  have heps : ∀ x, |v x-ψ x| < ε₀ := by
    intro x
    rcases hcases x with hh|⟨i,hi,hei⟩
    · simpa only [hh.self_of_nhds,sub_self,abs_zero] using hε₀
    · rw [hei.self_of_nhds]
      exact (hN i d).2.2.2.1 x
  have hglobal : ∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    intro x hx
    rcases hcases x with hh|⟨i,hi,hei⟩
    · obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hh
      refine ⟨hg ▸ ha x hx,hS.mpr (hstrict x hx),?_⟩
      rw [actualProfileSpeed_eventuallyEq g hh]
      have hn := actualCoordinateNorm_nonneg g x (coordinateMetricGradient g ψ x)
      change 0 ≤ actualProfileSpeed g ψ x at hn
      nlinarith
    · have hp := (hN i d).2.2.2.2 x hi
      obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hei
      exact ⟨hg ▸ hp.1,hS.mpr hp.2.1,(actualProfileSpeed_eventuallyEq g hei).symm ▸ hp.2.2.1⟩
  let B : Set E := {x | profileTorusQuotient ((N:ℝ) • yg x+τ) ∈
    ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ}
  have hBm : MeasurableSet B := (measurableSet_ball.prod measurableSet_ball).preimage
    (continuous_profileTorusQuotient.measurable.comp ((hyg.const_smul (N:ℝ)).add_const τ))
  refine ⟨v,B ∩ D,hv,hcpt,hsub,heps,hglobal,hBm.inter hDm,inter_subset_right.trans hDU,?_,?_⟩
  · rw [Measure.restrict_apply_univ,Measure.restrict_apply hBm] at hτ
    exact (mul_le_mul_left hMD _).trans hτ
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx.2
    rw [actualProfileSpeed_eventuallyEq g (heq i x (hCχ i hi))]
    apply ((hN i d).2.2.2.2 x (hCχ i hi)).2.2.2 (hχ1 i x hi)
    rw [hphase x i hi]
    exact hwindow _ hx.1

end
end YauCounterexamples

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.actual_metric_radial_finite_oai.{u_1} := @OAI.YauCounterexamples.actual_metric_radial_finite_oai.{u_1}
