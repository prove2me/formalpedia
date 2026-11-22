-- Prove2me | solution 1 for PHarmJetEquicontinuity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:19:26.314803+00:00
-- url     : https://prove2.me/submissions/fba95d91-4337-4afe-a4f1-4d50a805067b

import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_FirstOrderEstimateInput
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Theorems.Thm_PHarmNormalize


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (x₀ : Plane) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (v : Plane → ℝ) (g : Plane → Plane)
    (hv : IsPHarm p (Metric.ball x₀ (2 * R)) v g)
    (hbd : ∀ z ∈ Metric.ball x₀ (2 * R), |v z| ≤ M) :
    ContDiffOn ℝ 1 v (Metric.ball x₀ (3 * R / 2)) ∧
    (∀ z ∈ Metric.ball x₀ (3 * R / 2), ‖gradient v z‖ ≤ F.C₀ * M / (2 * R)) ∧
    (∀ z ∈ Metric.ball x₀ (3 * R / 2), ∀ z' ∈ Metric.ball x₀ (3 * R / 2),
      ‖gradient v z - gradient v z'‖
        ≤ F.C₀ * M / (2 * R) * (‖z - z'‖ / (2 * R)) ^ F.kappa) := by
  have hlam : (0 : ℝ) < 2 * R := by linarith
  have hlamne : (2 * R : ℝ) ≠ 0 := ne_of_gt hlam
  -- Step 1: normalize to the unit ball.  `PHarmNormalize` with `r = 2R`, `c = 0`.
  have hnorm := PHarmNormalize p hp hp2 (Metric.ball x₀ (2 * R)) v g x₀ (2 * R) M 0 hlam hM hv
  have hset : {x : Plane | x₀ + (2 * R) • x ∈ Metric.ball x₀ (2 * R)} = Metric.ball 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    constructor
    · intro h; nlinarith [norm_nonneg x]
    · intro h; nlinarith [norm_nonneg x]
  rw [hset] at hnorm
  -- Step 2: the normalized function is bounded by `1` on the unit ball.
  have hbd1 : ∀ x ∈ Metric.ball (0 : Plane) 1, |(v (x₀ + (2 * R) • x) - 0) / M| ≤ 1 := by
    intro x hx
    have hmem : x₀ + (2 * R) • x ∈ Metric.ball x₀ (2 * R) := by
      rw [← hset] at hx; exact hx
    rw [sub_zero, abs_div, abs_of_pos hM, div_le_one hM]
    exact hbd _ hmem
  -- Step 3: apply the first-order estimate datum.
  obtain ⟨hwC, hwbd, hwhol⟩ := F.est _ _ hnorm hbd1
  -- Step 4: transport back.  `S` maps `ball x₀ (3R/2)` into `ball 0 (3/4)`.
  have hSmem : ∀ z ∈ Metric.ball x₀ (3 * R / 2),
      (2 * R)⁻¹ • (z - x₀) ∈ Metric.ball (0 : Plane) (3 / 4) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hlam, inv_mul_eq_div, div_lt_iff₀ hlam]
    linarith
  -- `T ∘ S = id`, hence `v = M * (W ∘ S)` as functions on the whole plane.
  have hTS : ∀ z : Plane, x₀ + (2 * R) • ((2 * R)⁻¹ • (z - x₀)) = z := by
    intro z
    rw [smul_smul, mul_inv_cancel₀ hlamne, one_smul]
    abel
  have hvfun :
      (fun z : Plane => M * ((v (x₀ + (2 * R) • ((2 * R)⁻¹ • (z - x₀))) - 0) / M)) = v := by
    funext z
    rw [hTS z, sub_zero]
    field_simp
  -- The chain rule, done in `fderiv` and transferred to `gradient` through `toDual`.
  have hchain : ∀ z ∈ Metric.ball x₀ (3 * R / 2),
      gradient v z = (M / (2 * R))
        • gradient (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M) ((2 * R)⁻¹ • (z - x₀)) := by
    intro z hz
    have hy := hSmem z hz
    have hWd : HasFDerivAt (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M)
        (fderiv ℝ (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M) ((2 * R)⁻¹ • (z - x₀)))
        ((2 * R)⁻¹ • (z - x₀)) :=
      (((hwC.differentiableOn one_ne_zero) _ hy).differentiableAt
        (Metric.isOpen_ball.mem_nhds hy)).hasFDerivAt
    have hSd : HasFDerivAt (fun y : Plane => (2 * R)⁻¹ • (y - x₀))
        ((2 * R)⁻¹ • ContinuousLinearMap.id ℝ Plane) z :=
      ((hasFDerivAt_id z).sub_const x₀).const_smul ((2 * R)⁻¹)
    have hvd : HasFDerivAt v
        (M • ((fderiv ℝ (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M)
            ((2 * R)⁻¹ • (z - x₀))).comp
          ((2 * R)⁻¹ • ContinuousLinearMap.id ℝ Plane))) z := by
      have h := ((hWd.comp z hSd).const_mul M)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      exact (congrFun hvfun y).symm
    have hfd : fderiv ℝ v z
        = (M / (2 * R)) • fderiv ℝ (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M)
            ((2 * R)⁻¹ • (z - x₀)) := by
      rw [hvd.fderiv]
      ext y
      simp [smul_smul, div_eq_mul_inv]
    refine (InnerProductSpace.toDual ℝ Plane).injective ?_
    rw [toDual_gradient, map_smul, toDual_gradient, hfd]
  -- `S` is a difference of affine maps, so its increments scale by `(2R)⁻¹`.
  have hSdiff : ∀ z z' : Plane,
      (2 * R)⁻¹ • (z - x₀) - (2 * R)⁻¹ • (z' - x₀) = (2 * R)⁻¹ • (z - z') := by
    intro z z'
    rw [← smul_sub]
    congr 1
    abel
  refine ⟨?_, ?_, ?_⟩
  · -- `v` is `C^1` on the smaller ball: transport `w`'s regularity through the affine map.
    have hS1 : ContDiff ℝ 1 (fun y : Plane => (2 * R)⁻¹ • (y - x₀)) :=
      ContDiff.const_smul _ (contDiff_id.sub contDiff_const)
    have hc := hwC.comp hS1.contDiffOn fun z hz => hSmem z hz
    refine (ContDiffOn.const_smul M hc).congr fun z _ => ?_
    rw [smul_eq_mul]
    exact (congrFun hvfun z).symm
  · -- Step 5: the gradient bound.
    intro z hz
    rw [hchain z hz, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < M / (2 * R))]
    have h1 := hwbd _ (hSmem z hz)
    have h2 : (0 : ℝ) < M / (2 * R) := by positivity
    calc M / (2 * R)
          * ‖gradient (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M) ((2 * R)⁻¹ • (z - x₀))‖
        ≤ M / (2 * R) * F.C₀ := by exact mul_le_mul_of_nonneg_left h1 h2.le
      _ = F.C₀ * M / (2 * R) := by ring
  · -- Step 6: the Holder bound.
    intro z hz z' hz'
    rw [hchain z hz, hchain z' hz', ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < M / (2 * R))]
    have h1 := hwhol _ (hSmem z hz) _ (hSmem z' hz')
    have h2 : (0 : ℝ) < M / (2 * R) := by positivity
    have hnormS : ‖(2 * R)⁻¹ • (z - x₀) - (2 * R)⁻¹ • (z' - x₀)‖ = ‖z - z'‖ / (2 * R) := by
      rw [hSdiff z z', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlam, inv_mul_eq_div]
    rw [hnormS] at h1
    calc M / (2 * R)
          * ‖gradient (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M) ((2 * R)⁻¹ • (z - x₀))
              - gradient (fun x : Plane => (v (x₀ + (2 * R) • x) - 0) / M)
                  ((2 * R)⁻¹ • (z' - x₀))‖
        ≤ M / (2 * R) * (F.C₀ * (‖z - z'‖ / (2 * R)) ^ F.kappa) :=
          mul_le_mul_of_nonneg_left h1 h2.le
      _ = F.C₀ * M / (2 * R) * (‖z - z'‖ / (2 * R)) ^ F.kappa := by ring
