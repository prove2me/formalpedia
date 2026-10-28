-- Prove2me | solution 1 for OAI.YauCounterexamples.actual_radialCorrugation_strict_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:21:57.637448+00:00
-- url     : https://prove2.me/submissions/dc24abfb-aa6e-4f6b-b1c4-72ca2681e818

import Mathlib
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007
import Theorems.Thm_OAI_YauCounterexamples_radial_uniform_strict_bundle

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

theorem radialSquaredBase_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (b : ℝ) (x v w : ProfilePlane) :
    fderiv ℝ (fun z => fderiv ℝ (radialSquaredBase β b) z w) x v =
      4*deriv β (x.1^2+x.2^2)*(x.1*v.1+x.2*v.2)*(x.1*w.1+x.2*w.2) +
      2*β (x.1^2+x.2^2)*(v.1*w.1+v.2*w.2) := by
  have hβd := (hβ.differentiable (by simp) (x.1^2+x.2^2)).hasDerivAt
  have hp := hβd.comp_hasFDerivAt x (profileRadiusSquared_hasFDeriv x)
  have hi := ((hasFDerivAt_fst (𝕜:=ℝ) (p:=x)).mul_const w.1).add
    ((hasFDerivAt_snd (𝕜:=ℝ) (p:=x)).mul_const w.2)
  have hh := (hp.const_mul 2).mul hi
  have he : (fun z => fderiv ℝ (radialSquaredBase β b) z w) =
      (fun z => 2*β (z.1^2+z.2^2)*(z.1*w.1+z.2*w.2)) := by
    funext z; exact radialSquaredBase_first hβ b z w
  rw [he]
  erw [hh.fderiv]
  simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,Pi.add_apply]
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

lemma radialSquaredBase_radial_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (b : ℝ) (z v w : ProfilePlane) :
    fderiv ℝ (fun p => fderiv ℝ (radialSquaredBase β b) p w) z v =
      (2*β (z.1^2+z.2^2)+4*(z.1^2+z.2^2)*deriv β (z.1^2+z.2^2))*
        planeRadialCovector z v*planeRadialCovector z w+
      (2*β (z.1^2+z.2^2))*planeAngularCovector z v*planeAngularCovector z w := by
  rw [radialSquaredBase_second hβ]
  by_cases hz : z = 0
  · simp [hz,hβ0]
  · have hs := plane_radius_pos hz
    have hs2 := Real.sq_sqrt (show 0 ≤ z.1^2+z.2^2 by positivity)
    simp only [planeRadialCovector,planeAngularCovector,ite_eq_right hz,
      _root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp
    rw [hs2]
    ring



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

theorem profilePeriodize_second {f : ProfilePlane → ℝ} {R : ℝ}
    (hR : 2*R < 1) (hf : ∀ z, R < ‖z‖ → f z = 0)
    (hs : ContDiff ℝ ∞ f) (k : ProfileLattice) {x : ProfilePlane}
    (hx : ‖x-profileLatticePoint k‖ < R) (v w : ProfilePlane) :
    fderiv ℝ (fun z => fderiv ℝ (profilePeriodize f) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ f z w) (x-profileLatticePoint k) v := by
  have ho : IsOpen {z : ProfilePlane | ‖z-profileLatticePoint k‖ < R} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have he : (fun z => fderiv ℝ (profilePeriodize f) z w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ f (z-profileLatticePoint k) w) := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact profilePeriodize_first hR hf (hs.differentiable (by simp)) k hz w
  rw [he.fderiv_eq]
  have hD := (hs.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hh := ((hD (x-profileLatticePoint k)).clm_apply
    (differentiableAt_const w)).hasFDerivAt.comp x
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

theorem periodicRadialFunction_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hsmall : 2*R < 1) (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x v w : ProfilePlane) :
    fderiv ℝ (fun p => fderiv ℝ (periodicRadialFunction β b) p w) x v =
      periodicRadialSecond β R x * planeRadialCovector (periodicRadialOffset R x) v *
        planeRadialCovector (periodicRadialOffset R x) w+
      periodicAngularSecond β R x * planeAngularCovector (periodicRadialOffset R x) v *
        planeAngularCovector (periodicRadialOffset R x) w := by
  unfold periodicRadialFunction
  simp only [fderiv_const_add]
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 :=
    fun z hz => hf z (hrR.trans hz)
  by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
  · simp only [periodicRadialSecond,periodicAngularSecond,
      periodicRadialOffset,dite_eq_left hx]
    rw [profilePeriodize_second hsmall hfR
      (radialSquaredBase_smooth β b hβ) hx.choose hx.choose_spec]
    exact radialSquaredBase_radial_second hβ hβ0 b _ v w
  · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
    have he := profilePeriodize_eventually_zero hrR hf x hxn
    have he' : (fun p => fderiv ℝ (profilePeriodize (radialSquaredBase β b)) p w)
        =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with p hp
      simp [hp]
    have hz := congrArg (fun L : ProfilePlane →L[ℝ] ℝ => L v) (he'.fderiv_eq (𝕜 := ℝ))
    simpa [periodicRadialFunction,periodicRadialSecond,periodicAngularSecond,
      periodicRadialOffset,hx,hβ0] using hz

lemma norm_planeRadialCovector_le (z : ProfilePlane) : ‖planeRadialCovector z‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have hsq := plane_radial_angular_sq z v
  have h1 : |v.1| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_left |v.1| |v.2|
  have h2 : |v.2| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right |v.1| |v.2|
  rw [Real.norm_eq_abs]
  have hs1 : v.1^2 ≤ ‖v‖^2 := by nlinarith only [h1,sq_abs v.1,norm_nonneg v,abs_nonneg v.1]
  have hs2 : v.2^2 ≤ ‖v‖^2 := by nlinarith only [h2,sq_abs v.2,norm_nonneg v,abs_nonneg v.2]
  nlinarith only [hsq,hs1,hs2,sq_nonneg (planeAngularCovector z v),
    sq_abs (planeRadialCovector z v),abs_nonneg (planeRadialCovector z v),norm_nonneg v]


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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

local instance genericHessMapNorm_rc79748_1 : NormedAddCommGroup (E →L[ℝ] V) := inferInstance
attribute [local instance] OAI.YauCounterexamples.genericHessMapSpace
local instance genericHessFormNorm_rc79748_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := inferInstance
local instance genericHessFormSpace_rc79748_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := inferInstance
lemma continuous_coordinateCovariantSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ) {f : E → V}
    (hf : ContDiff ℝ ∞ f) : Continuous (coordinateCovariantSecond Γ f) := by
  apply Continuous.sub
  · exact (hf.fderiv_right (m:=(∞ : ℕ∞ω)) (by simp)).continuous_fderiv
      (by simp)
  · exact ((ContinuousLinearMap.compL ℝ E E V).continuous.comp
      (hf.continuous_fderiv (by simp))).clm_comp hΓ

end GenericCoordinateHessian


end

section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma second_directional_eq {f : E → V} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ f z w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply
    ((hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

lemma smooth_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (F ∘ y) z w) x v =
      fderiv ℝ (fderiv ℝ F) (y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      fderiv ℝ F (y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hdF := hF.differentiable (by simp)
  have hdy := hy.differentiable (by simp)
  have hdDF := (hF.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hdDy := (hy.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (F ∘ y) z w) =
      (fun z => fderiv ℝ F (y z) (fderiv ℝ y z w)) := by
    funext z
    rw [fderiv_comp z (hdF _) (hdy _),ContinuousLinearMap.comp_apply]
  rw [he]
  erw [fderiv_clm_apply ((hdDF _).comp x (hdy _))
    ((hdDy x).clm_apply (differentiableAt_const w))]
  erw [fderiv_fun_comp x (hdDF _) (hdy _)]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma smooth_product_second {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t*g t) z w) x v =
      f x * fderiv ℝ (fun z => fderiv ℝ g z w) x v +
      fderiv ℝ f x v * fderiv ℝ g x w +
      fderiv ℝ f x w * fderiv ℝ g x v +
      g x * fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t*g t) z w) =
      (fun z => f z * fderiv ℝ g z w + g z * fderiv ℝ f z w) := by
    funext z
    rw [fderiv_fun_mul (df z) (dg z)]
    simp
  rw [he]
  erw [fderiv_fun_add ((df x).mul ((dDg x).clm_apply (differentiableAt_const w)))
    ((dg x).mul ((dDf x).clm_apply (differentiableAt_const w))),
    fderiv_fun_mul (df x) ((dDg x).clm_apply (differentiableAt_const w)),
    fderiv_fun_mul (dg x) ((dDf x).clm_apply (differentiableAt_const w))]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

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
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma smooth_sum_second {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => f t+g t) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v +
      fderiv ℝ (fun z => fderiv ℝ g z w) x v := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have dDg := (hg.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => f t+g t) z w) =
      (fun z => fderiv ℝ f z w + fderiv ℝ g z w) := by
    funext z; rw [fderiv_fun_add (df z) (dg z)]; rfl
  rw [he, fderiv_fun_add ((dDf x).clm_apply (differentiableAt_const w))
    ((dDg x).clm_apply (differentiableAt_const w))]
  rfl
lemma smooth_const_smul_second {f : E → V}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => c • f t) z w) x v =
      c • fderiv ℝ (fun z => fderiv ℝ f z w) x v := by
  have df := hf.differentiable (by simp)
  have dDf := (hf.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)).differentiable (by simp)
  have he : (fun z => fderiv ℝ (fun t => c • f t) z w) =
      (fun z => c • fderiv ℝ f z w) := by
    funext z; rw [fderiv_fun_const_smul (df z) c]; rfl
  rw [he, fderiv_fun_const_smul ((dDf x).clm_apply (differentiableAt_const w)) c]
  rfl

lemma scaled_comp_second {F : V → ℝ} {y : E → V}
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v =
      N^2 * fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      N * fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) := by
  have hh := smooth_comp_second hF (hy.const_smul N) x v w
  change fderiv ℝ (fun z => fderiv ℝ (fun t => F (N • y t)) z w) x v = _ at hh
  rw [fderiv_fun_const_smul (hy.differentiable (by simp) x) N,
    smooth_const_smul_second hy N x v w] at hh
  simp only [_root_.smul_apply,map_smul,smul_eq_mul] at hh
  rw [hh]
  ring

theorem corrugation_second {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => ψ t+c*(χ t*F (N • y t))) z w) x v =
      fderiv ℝ (fun z => fderiv ℝ ψ z w) x v +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (fderiv ℝ (fun z => fderiv ℝ y z w) x v) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*fderiv ℝ (fun z => fderiv ℝ χ z w) x v := by
  have hg : ContDiff ℝ ∞ (fun t => F (N • y t)) := hF.comp (hy.const_smul N)
  have hh := smooth_sum_second hψ ((hχ.mul hg).const_smul c) x v w
  simp only [smul_eq_mul] at hh
  rw [hh]
  have hc := smooth_const_smul_second (hχ.mul hg) c x v w
  simp only [smul_eq_mul] at hc
  rw [hc,smooth_product_second hχ hg x v w,scaled_comp_second hF hy N x v w]
  have hfirst (z : E) : fderiv ℝ (fun t => F (N • y t)) x z =
      N * fderiv ℝ F (N • y x) (fderiv ℝ y x z) := by
    erw [fderiv_fun_comp x (hF.differentiable (by simp) _) ((hy.differentiable (by simp) x).const_smul N),
      fderiv_fun_const_smul (hy.differentiable (by simp) x) N]
    simp
  rw [hfirst w,hfirst v]
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

theorem periodicRadialFunction_fderiv_bound {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβp : ∀ t, 0 ≤ β t)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) (x : ProfilePlane) :
    ‖fderiv ℝ (periodicRadialFunction β b) x‖ ≤ 2*periodicRadialSpeed β R x := by
  have he : fderiv ℝ (periodicRadialFunction β b) x =
      periodicRadialSpeed β R x • planeRadialCovector (periodicRadialOffset R x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact periodicRadialFunction_first hβ hβ0 hr hrR hsmall hb hzero x v
  have hp : 0 ≤ periodicRadialSpeed β R x := by
    unfold periodicRadialSpeed
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (hβp _)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]
  nlinarith only [mul_le_mul_of_nonneg_left (norm_planeRadialCovector_le (periodicRadialOffset R x)) hp]


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

lemma periodicRadialSpeed_le_angular {β : ℝ → ℝ} (hβ : ∀ t, 0 ≤ β t)
    {R : ℝ} (hR : 0 < R) (x : ProfilePlane) :
    periodicRadialSpeed β R x/(2*R) ≤ periodicAngularSecond β R x := by
  let z := periodicRadialOffset R x
  let t := z.1^2+z.2^2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htb : t ≤ 2*R^2 := periodicRadialOffset_radius_sq_le hR.le x
  have hs : Real.sqrt t ≤ 2*R := by
    nlinarith only [Real.sq_sqrt ht,Real.sqrt_nonneg t,htb,hR]
  apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
  change 2*Real.sqrt t*β t ≤ (2*β t)*(2*R)
  nlinarith only [mul_le_mul_of_nonneg_right hs (hβ t)]

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
section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinateCovariantSecond_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    coordinateCovariantSecond Γ f x v w =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v - fderiv ℝ f x (Γ x v w) := by
  rw [second_directional_eq hf]
  rfl

theorem corrugation_covariant_second
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    coordinateCovariantSecond Γ (fun z => ψ z+c*(χ z*F (N • y z))) x v w =
      coordinateCovariantSecond Γ ψ x v w +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  have hP : ContDiff ℝ ∞ (fun z => ψ z+c*(χ z*F (N • y z))) :=
    hψ.add (contDiff_const.mul (hχ.mul (hF.comp (hy.const_smul N))))
  have hfirst : fderiv ℝ (fun z => ψ z+c*(χ z*F (N • y z))) x (Γ x v w) =
      fderiv ℝ ψ x (Γ x v w) + c*fderiv ℝ χ x (Γ x v w)*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x (Γ x v w)) := by
    convert corrugation_first hψ hχ hF hy c N x (Γ x v w) using 1; congr 2
    funext z
    ring
  rw [coordinateCovariantSecond_apply Γ hP,
    corrugation_second hψ hχ hF hy,hfirst,
    coordinateCovariantSecond_apply Γ hψ,
    coordinateCovariantSecond_apply Γ hy,
    coordinateCovariantSecond_apply Γ hχ,map_sub]
  ring

lemma corrugationSecondRemainder_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x v w : E) :
    corrugationSecondRemainder Γ ψ χ F y d N x v w =
      d*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      d*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      d*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      (d/N)*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  change coordinateCovariantSecond Γ _ x v w - coordinateCovariantSecond Γ ψ x v w -
    (d*N*χ x)*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) = _
  rw [corrugation_covariant_second Γ hψ hχ hF hy]
  field_simp [hN]
  ring

theorem corrugationSecondRemainder_norm_bound
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x : E) :
    ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
      |d| * |χ x| * ‖fderiv ℝ F (N • y x)‖ * ‖coordinateCovariantSecond Γ y x‖ +
      2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖ * ‖fderiv ℝ y x‖ +
      |d / N| * |F (N • y x)| * ‖coordinateCovariantSecond Γ χ x‖ := by
  let DF := fderiv ℝ F (N • y x)
  let Dy := fderiv ℝ y x
  let Dχ := fderiv ℝ χ x
  let Hy := coordinateCovariantSecond Γ y x
  let Hχ := coordinateCovariantSecond Γ χ x
  apply (corrugationSecondRemainder Γ ψ χ F y d N x).opNorm_le_bound₂
    (by positivity)
  intro v w
  rw [corrugationSecondRemainder_apply Γ hψ hχ hF hy d N hN]
  have hyterm : ‖d * χ x * DF (Hy v w)‖ ≤
      |d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * |χ x| * (‖DF‖ * (‖Hy‖ * ‖v‖ * ‖w‖)) := by
        gcongr
        exact (DF.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (Hy.le_opNorm₂ v w) (norm_nonneg _))
      _ = _ := by ring
  have hcross (v w : E) : ‖d * Dχ v * DF (Dy w)‖ ≤
      |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * (‖Dχ‖ * ‖v‖) * (‖DF‖ * (‖Dy‖ * ‖w‖)) := by
        gcongr
        · exact Dχ.le_opNorm v
        · exact (DF.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (Dy.le_opNorm w) (norm_nonneg _))
      _ = _ := by ring
  have hχterm : ‖(d / N) * F (N • y x) * Hχ v w‖ ≤
      |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d / N| * |F (N • y x)| * (‖Hχ‖ * ‖v‖ * ‖w‖) := by
        gcongr
        exact Hχ.le_opNorm₂ v w
      _ = _ := by ring
  calc
    _ ≤ (‖d * χ x * DF (Hy v w)‖ + ‖d * Dχ v * DF (Dy w)‖ +
        ‖d * Dχ w * DF (Dy v)‖) + ‖(d / N) * F (N • y x) * Hχ v w‖ :=
      (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (|d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖w‖ * ‖v‖) +
        |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ :=
      add_le_add (add_le_add (add_le_add hyterm (hcross v w)) (hcross w v)) hχterm
    _ = _ := by dsimp [DF, Dy, Dχ, Hy, Hχ]; ring


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
lemma pulledGradient_norm_le (j : V →L[ℝ] E) (u : E → ℝ) (x : E) :
    ‖pulledGradient j u x‖ ≤ ‖fderiv ℝ u x‖*‖j‖ := by
  rw [pulledGradient,LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_comp_le _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma pulledRadialLeading_decomposition (j : V →L[ℝ] E) (y : E → ProfilePlane)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) (N : ℝ) (x : E) (v w : V) :
    let z := periodicRadialOffset R (N • y x)
    let D := (fderiv ℝ y x).comp j
    pulledRadialLeading j y β b N x v w =
      periodicRadialSecond β R (N • y x)*planeRadialCovector z (D v)*planeRadialCovector z (D w) +
      periodicAngularSecond β R (N • y x)*planeAngularCovector z (D v)*planeAngularCovector z (D w) := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) := radial_periodic_smooth hβ hr hb hzero
  dsimp [pulledRadialLeading]
  rw [←second_directional_eq hF]
  exact periodicRadialFunction_second hβ hβ0 hr hrR hsmall hb hzero _ _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma radialCorrugation_hessian (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ) (b δ A N : ℝ) (x : E) :
    pulledHessian Γ j (radialCorrugation ψ χ y β b δ A N) x =
      pulledHessian Γ j ψ x+(N*δ*A*χ x) • pulledRadialLeading j y β b N x +
        pulledRadialRemainder Γ j ψ χ y β b δ A N x := by
  unfold radialCorrugation
  ext v w
  simp only [pulledHessian,pulledRadialLeading,pulledRadialRemainder,
    corrugationSecondRemainder,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply,add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_QuadraticRemainderSecondBound
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
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

lemma quadratic_remainder_of_second_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖^2 := by
  have hdf := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have hL (z : E) : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C*‖z-x‖ :=
    (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf.differentiable (by simp) z) (fun z _ => hb z) (mem_univ x) (mem_univ z)
  let R := fun z => f z - f x - fderiv ℝ f x (z-x)
  have hR (z : E) : HasFDerivAt R (fderiv ℝ f z - fderiv ℝ f x) z := by
    convert ((hf.differentiable (by simp) z).hasFDerivAt.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)) using 1 <;> rfl
  have hrbound (z : E) (hz : z ∈ closedBall x ‖y-x‖) :
      ‖fderiv ℝ R z‖ ≤ C*‖y-x‖ := by
    rw [(hR z).fderiv]
    exact (hL z).trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hz) hC)
  have hh := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hR z).differentiableAt) hrbound
    (mem_closedBall_self (norm_nonneg _))
    (show y ∈ closedBall x ‖y-x‖ by simp [dist_eq_norm])
  simpa only [R,sub_self,map_zero,sub_zero,pow_two,mul_assoc] using hh

theorem cutoff_gradient_square_bound {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 < C)
    (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x : E) :
    ‖fderiv ℝ f x‖^2 ≤ 4*C*f x := by
  let v := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hv : ‖v‖ = ‖fderiv ℝ f x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hd : fderiv ℝ f x v = ‖v‖^2 := by
    rw [←InnerProductSpace.toDual_symm_apply]
    exact real_inner_self_eq_norm_sq v
  let t : ℝ := (2*C)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  have htc : t*(2*C) = 1 := inv_mul_cancel₀ (by positivity)
  have he := quadratic_remainder_of_second_bound hf hC.le hb x (x-t • v)
  have hyn := hn (x-t • v)
  have hs : x-t • v-x = -(t • v) := by abel
  simp only [hs,map_neg,map_smul,smul_eq_mul,hd,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_pos ht] at he
  have hupper := (le_abs_self (f (x-t • v)-f x- -(t*‖v‖^2))).trans he
  have hsmall : t*‖v‖^2 ≤ f x+C*t^2*‖v‖^2 := by nlinarith
  have hcoeff : C*t^2 = t/2 := by nlinarith [htc]
  rw [hcoeff] at hsmall
  have hres : ‖v‖^2 ≤ 4*C*f x := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2*C by positivity)
    nlinarith [htc]
  simpa only [hv] using hres

theorem exists_cutoff_sqrt_gradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hn : ∀ x, 0 ≤ f x) :
    ∃ C > 0, ∀ x, ‖fderiv ℝ f x‖ ≤ C * Real.sqrt (f x) := by
  have hd := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  have hdd := hd.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  obtain ⟨B,hB⟩ := hdd.continuous.bounded_above_of_compact_support ((hs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Real.sqrt (4*C),Real.sqrt_pos.mpr (by positivity),fun x => ?_⟩
  have hh := cutoff_gradient_square_bound hf hn hC (fun y => (hB y).trans (le_max_left _ _)) x
  have hs1 := Real.sq_sqrt (show 0 ≤ 4*C by positivity)
  have hs2 := Real.sq_sqrt (hn x)
  have hp : 0 ≤ Real.sqrt (4*C)*Real.sqrt (f x) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (‖fderiv ℝ f x‖ + Real.sqrt (4*C)*Real.sqrt (f x))]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ActualRadialCorrugationStrict
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

lemma cutoff_small_product_bound (χ D f J M : ℝ)
    (hχ : 0 ≤ χ) (_hD : 0 ≤ D) (hf : 0 ≤ f) (hfM : f ≤ M)
    (hJ : 0 ≤ J) (hcut : D ≤ J*Real.sqrt χ) :
    (χ+D)*f ≤ χ*f+J*Real.sqrt M*Real.sqrt (χ*f) := by
  have he : Real.sqrt χ*f = Real.sqrt f*Real.sqrt (χ*f) := by
    rw [Real.sqrt_mul hχ]
    calc
      _ = Real.sqrt χ*((Real.sqrt f)^2) := by rw [Real.sq_sqrt hf]
      _ = _ := by ring
  have hh : Real.sqrt χ*f ≤ Real.sqrt M*Real.sqrt (χ*f) := by
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfM) (Real.sqrt_nonneg _)
  calc
    _ ≤ (χ+J*Real.sqrt χ)*f := mul_le_mul_of_nonneg_right (by linarith) hf
    _ = χ*f+J*(Real.sqrt χ*f) := by ring
    _ ≤ χ*f+J*(Real.sqrt M*Real.sqrt (χ*f)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hJ)
    _ = _ := by ring


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



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateCovariantSecondAddConst
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma coordinateCovariantSecond_add_const (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (y : E → V) (d : V) (x : E) :
    coordinateCovariantSecond Γ (fun z => y z+d) x = coordinateCovariantSecond Γ y x := by
  have hh : fderiv ℝ (fun z => y z+d) = fderiv ℝ y := funext fun _ => fderiv_add_const d
  simp only [coordinateCovariantSecond, hh]

omit [FiniteDimensional ℝ E] in
theorem corrugationSecondRemainder_uniform_shift
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ d₀ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F (fun z => y z+d₀) d N x‖ ≤
        C * ((|χ x| + ‖fderiv ℝ χ x‖) * ‖fderiv ℝ F (N • (y x+d₀))‖ + N⁻¹) := by
  obtain ⟨Y₂, hY₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ y)
    (continuous_coordinateCovariantSecond Γ hΓ hy).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y)
    (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨χ₂, hχ₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ χ)
    (continuous_coordinateCovariantSecond Γ hΓ hχ).continuousOn
  let c₁ := |d| * |Y₂|
  let c₂ := 2 * |d| * |Y₁|
  let c₃ := |d| * |B| * |χ₂|
  let C := 1 + c₁ + c₂ + c₃
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hc₁C : c₁ ≤ C := by dsimp [C]; linarith
  have hc₂C : c₂ ≤ C := by dsimp [C]; linarith
  have hc₃C : c₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN d₀ x hx
  have hY₂x := (hY₂ x hx).trans (le_abs_self Y₂)
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hχ₂x := (hχ₂ x hx).trans (le_abs_self χ₂)
  have hBx := (hB (N • (y x+d₀))).trans (le_abs_self B)
  calc
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖ * ‖coordinateCovariantSecond Γ y x‖ +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖ * ‖fderiv ℝ y x‖ +
        |d / N| * |F (N • (y x+d₀))| * ‖coordinateCovariantSecond Γ χ x‖ :=
      by
      simpa only [fderiv_add_const,coordinateCovariantSecond_add_const] using
        corrugationSecondRemainder_norm_bound Γ hψ hχ hF (hy.add (contDiff_const (c:=d₀))) d N (ne_of_gt hN) x
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖ * |Y₂| +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖ * |Y₁| +
        |d / N| * |B| * |χ₂| := by gcongr
    _ = c₁ * (|χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖) +
        c₂ * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖) + c₃ * N⁻¹ := by
      rw [abs_div, abs_of_pos hN]
      dsimp [c₁, c₂, c₃]
      ring
    _ ≤ C * (|χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖) +
        C * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖) + C * N⁻¹ := by gcongr
    _ = _ := by ring

theorem corrugationSecondRemainder_small_product_scaled_shift
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχn : ∀ x, 0 ≤ χ x)
    (f : V → ℝ) (M Jf : ℝ) (hJf : 0 ≤ Jf)
    (hfn : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (hDf : ∀ z, ‖fderiv ℝ F z‖ ≤ Jf*f z)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ d₀ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F (fun z => y z+d₀) d N x‖ ≤
        C * (χ x*f (N • (y x+d₀))+Real.sqrt (χ x*f (N • (y x+d₀)))+N⁻¹) := by
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_uniform_shift Γ hΓ hψ hχ hF hy K hK d B hB
  obtain ⟨J,hJ,hcut⟩ := exists_cutoff_sqrt_gradient hχ hχs hχn
  let c := J*Real.sqrt M
  have hc : 0 ≤ c := mul_nonneg hJ.le (Real.sqrt_nonneg _)
  refine ⟨C₀*(1+Jf)*(1+c),by positivity,?_⟩
  intro N hN d₀ x hx
  have ht : 0 ≤ χ x*f (N • (y x+d₀)) := mul_nonneg (hχn x) (hfn _)
  have hs := Real.sqrt_nonneg (χ x*f (N • (y x+d₀)))
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hprod : (χ x+‖fderiv ℝ χ x‖)*f (N • (y x+d₀)) ≤
      χ x*f (N • (y x+d₀))+c*Real.sqrt (χ x*f (N • (y x+d₀))) :=
    cutoff_small_product_bound _ _ _ _ _ (hχn x) (norm_nonneg _) (hfn _) (hfM _) hJ.le (hcut x)
  calc
    _ ≤ C₀*((|χ x|+‖fderiv ℝ χ x‖)*‖fderiv ℝ F (N • (y x+d₀))‖+N⁻¹) := hrem N hN d₀ x hx
    _ ≤ C₀*((χ x+‖fderiv ℝ χ x‖)*(Jf*f (N • (y x+d₀)))+N⁻¹) := by
      rw [abs_of_nonneg (hχn x)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hDf _)
          (add_nonneg (hχn x) (norm_nonneg _))) le_rfl) hC₀.le
    _ = C₀*(Jf*((χ x+‖fderiv ℝ χ x‖)*f (N • (y x+d₀)))+N⁻¹) := by ring
    _ ≤ C₀*(Jf*(χ x*f (N • (y x+d₀))+c*Real.sqrt (χ x*f (N • (y x+d₀))))+N⁻¹) := by gcongr
    _ ≤ C₀*((1+Jf)*(1+c)*(χ x*f (N • (y x+d₀))+Real.sqrt (χ x*f (N • (y x+d₀)))+N⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      have h1 := mul_nonneg hJf ht
      have h2 := mul_nonneg hc ht
      have h3 := mul_nonneg hJf hs
      have h4 := mul_nonneg hJf hNi
      have h5 := mul_nonneg hc hNi
      have h6 := mul_nonneg (mul_nonneg hJf hc) ht
      have h7 := mul_nonneg (mul_nonneg hJf hc) hNi
      have h8 := mul_nonneg hc hs
      nlinarith only [ht,hs,h1,h2,h3,h4,h5,h6,h7,h8]
    _ = _ := by ring

end
end YauCounterexamples

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


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_radialCorrugation_strict_shift_oai
    (K₀ : Set E) (hK₀ : IsCompact K₀) {V : K₀ → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (j : ∀ x, V x →L[ℝ] E) (J : ℝ) (hJ : 0 ≤ J) (hj : ∀ x, ‖j x‖ ≤ J)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (hβv : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmallR : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (Fmax K S : ℝ) (hFmax : 0 ≤ Fmax) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ K)
    (m α M Hmax δ A : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖pulledGradient (j x) ψ x‖)
    (haM : ∀ x, ‖pulledGradient (j x) ψ x‖ ≤ M)
    (hHH : ∀ x, ‖pulledHessian Γ (j x) ψ x‖ ≤ Hmax)
    (hAa : ∀ x, A ≤ 2*‖pulledGradient (j x) ψ x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (pulledGradient (j x) ψ x) w = 0 →
      m ≤ profileTrace (pulledHessian Γ (j x) ψ x) (pulledGradient (j x) ψ x) w)
    (hfirst : ∀ x : K₀, fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0)
    (hup : ∀ (x : K₀) v, Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖)
    (hlo : ∀ (x : K₀) v, inner ℝ (pulledGradient (j x) ψ x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2)) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, ∀ x : K₀,
      profileStrict (pulledHessian Γ (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x)
        (pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x) ∧
      pulledGradient (j x) (radialCorrugation ψ χ (fun z => y z+d) β b δ A N) x ≠ 0 := by
  let F := periodicRadialFunction β b
  have hF : ContDiff ℝ ∞ F := radial_periodic_smooth hβ hr hb hzero
  obtain ⟨B₀,hB₀,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmallR hb hzero
  obtain ⟨D,hD⟩ := hK₀.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  let Ce := |δ*A| *B₀*D'*J
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_small_product_scaled_shift Γ hΓ hψ hχ hF hy hχs
    (fun x => (hχv x).1) (periodicRadialSpeed β R) Fmax 2 (by norm_num)
    (fun z => (hcoef z).1) (fun z => (hcoef z).2.1)
    (periodicRadialFunction_fderiv_bound hβ hβ0 (fun t => (hβv t).1) hr hrR hsmallR hb hzero)
    K₀ hK₀ (δ*A) B₀ hBF
  let Cr := C₀*J^2
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  let X := K₀ × ProfilePlane
  let a : ∀ x : X, V x.1 := fun x => pulledGradient (j x.1) ψ x.1
  let H : ∀ x : X, ProfileForm (V x.1) := fun x => pulledHessian Γ (j x.1) ψ x.1
  let z : ℕ → X → ProfilePlane := fun N x => periodicRadialOffset R ((N:ℝ) • (y x.1+x.2))
  let D₁ : ∀ x : X, V x.1 →L[ℝ] ProfilePlane := fun x => (fderiv ℝ y x.1).comp (j x.1)
  let R₁ : ℕ → ∀ x : X, V x.1 →L[ℝ] ℝ := fun N x => (planeRadialCovector (z N x)).comp (D₁ x)
  let T₁ : ℕ → ∀ x : X, V x.1 →L[ℝ] ℝ := fun N x => (planeAngularCovector (z N x)).comp (D₁ x)
  let r₁ : ℕ → ∀ x : X, V x.1 := fun N x => (InnerProductSpace.toDual ℝ (V x.1)).symm (R₁ N x)
  let e : ℕ → ∀ x : X, V x.1 := fun N x => (δ*A/(N:ℝ)*F ((N:ℝ) • (y x.1+x.2))) • pulledGradient (j x.1) χ x.1
  let f : ℕ → X → ℝ := fun N x => periodicRadialSpeed β R ((N:ℝ) • (y x.1+x.2))
  let b₁ : ℕ → X → ℝ := fun N x => periodicAngularSecond β R ((N:ℝ) • (y x.1+x.2))
  let f₂ : ℕ → X → ℝ := fun N x => periodicRadialSecond β R ((N:ℝ) • (y x.1+x.2))
  let B : ℕ → ∀ x : X, ProfileForm (V x.1) := fun N x => pulledRadialLeading (j x.1) (fun t => y t+x.2) β b N x.1
  let Er : ℕ → ∀ x : X, ProfileForm (V x.1) := fun N x => pulledRadialRemainder Γ (j x.1) ψ χ (fun t => y t+x.2) β b δ A N x.1
  have hR : 0 < R := hr.trans_lt hrR
  have hframes (N : ℕ) (x : X) := radial_coframe_bounds (D₁ x) (a x) (z N x) (hfirst x.1) (hup x.1) (hlo x.1)
  have hnat : ∀ᶠ N : ℕ in atTop, 0 < (N:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact_mod_cast hN
  have he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ) := by
    filter_upwards [hnat] with N hN x
    have hg : ‖pulledGradient (j x.1) χ x.1‖ ≤ D'*J :=
      (pulledGradient_norm_le (j x.1) χ x.1).trans (mul_le_mul
        ((hD x.1 x.1.property).trans (le_max_left _ _)) (hj x.1) (norm_nonneg _) hD')
    dsimp only [e,Ce]
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hN]
    calc
      _ ≤ (|δ*A|/(N:ℝ)*B₀)*(D'*J) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hN.le)) hg
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹) := by
    filter_upwards [hnat] with N hN x
    have ht : 0 ≤ χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹ := by
      have hf : 0 ≤ f N x := (hcoef _).1
      have hχn : 0 ≤ χ x.1 := (hχv x.1).1
      positivity
    calc
      _ ≤ ‖corrugationSecondRemainder Γ ψ χ F (fun t => y t+x.2) (δ*A) N x.1‖*‖j x.1‖^2 :=
        norm_bilinear_pullback_le _ _
      _ ≤ (C₀*(χ x.1*f N x+Real.sqrt (χ x.1*f N x)+(N:ℝ)⁻¹))*J^2 :=
        mul_le_mul (hrem N hN x.2 x.1 x.1.property) (sq_le_sq₀ (norm_nonneg _) hJ |>.mpr (hj x.1))
          (sq_nonneg _) (mul_nonneg hC₀.le ht)
      _ = _ := by dsimp [Cr]; ring
  have hs := radial_uniform_strict_bundle (fun x : X => hd x.1) a H (fun x => χ x.1) r₁ e R₁ T₁ f b₁ f₂ B Er
    m α M Hmax δ A K S (2*R) Fmax Ce Cr hm hm1 hα hM hHmax hδ hA hK hS
    (by positivity) hFmax hCe hCr hsmall
    (fun x => ha0 x.1) (fun x => haM x.1) (fun x => hHH x.1) (fun x => hAa x.1)
    (fun x => hmargin x.1) (fun x => hχv x.1)
    (fun N x => ⟨(hcoef _).1,(hcoef _).2.1⟩)
    (fun N x => periodicRadialSpeed_le_angular (fun t => (hβv t).1) hR _)
    (fun N x => (hcoef _).2.2.1) (fun N x => (hcoef _).2.2.2)
    (fun N x v => InnerProductSpace.toDual_symm_apply)
    (fun N x => (hframes N x).1) (fun N x => (hframes N x).2.1)
    (fun N x => (hframes N x).2.2.1) (fun N x => (hframes N x).2.2.2)
    (fun N x v w => by
      simpa only [B,f₂,b₁,R₁,T₁,z,D₁,ContinuousLinearMap.comp_apply,fderiv_add_const] using pulledRadialLeading_decomposition (j x.1) (fun t => y t+x.2)
        hβ hβ0 hr hrR hsmallR hb hzero N x.1 v w)
    he hEr
  filter_upwards [hs,hnat] with N hsN hN d x
  rw [radialCorrugation_hessian,radialCorrugation_gradient hψ hχ (hy.add contDiff_const)
    hβ hβ0 hr hrR hsmallR hb hzero (j x) δ A N (ne_of_gt hN)]
  simpa only [fderiv_add_const] using hsN (x,d)

end
end YauCounterexamples

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.actual_radialCorrugation_strict_shift_oai.{u_1, u_2} := @OAI.YauCounterexamples.actual_radialCorrugation_strict_shift_oai.{u_1, u_2}
