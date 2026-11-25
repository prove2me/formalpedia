-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:33.714124+00:00
-- url     : https://prove2.me/submissions/e530d9bb-d967-463a-ae45-dee22f8fddaf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hn : 1 ≤ n) {P : Y}
    (hP : P ∈ A.zeroSet s) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v in 𝓝 (A.chart (A.pick P) P),
      ‖v - A.chart (A.pick P) P‖ ≤ K * ‖A.zLoc w0 s (A.pick P) v‖ := by
  set i := A.pick P
  set vP := A.chart i P
  set zL := A.zLoc w0 s i
  have hdet : (fderiv ℂ zL vP).det ≠ 0 := hD.coord P hP
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdiff : DifferentiableAt ℂ zL vP := by
    by_contra h
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt h]
    show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin]
    exact zero_pow (by omega)
  have hz0 : zL vP = 0 := by
    ext k
    simp only [zL, zLoc, PiLp.toLp_apply, vP, (A.chart i).left_inv (A.mem_pick P)]
    rw [hP k]; simp
  set D := fderiv ℂ zL vP
  set E := (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ u, ‖u‖ ≤ K0 * ‖D u‖ := by
    refine ⟨‖(E.symm : V n →L[ℂ] V n)‖, fun u => ?_⟩
    have h := E.antilipschitz.le_mul_dist u 0
    simp only [dist_zero_right, map_zero] at h
    exact h
  set K1 := max K0 1
  have hK1 : 0 < K1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlo := hdiff.hasFDerivAt.isLittleO
  have hev := hlo.def (show (0:ℝ) < 1 / (2 * K1) by positivity)
  refine ⟨2 * K1, by positivity, ?_⟩
  filter_upwards [hev] with v hv
  rw [hz0, sub_zero] at hv
  have h1 : ‖v - vP‖ ≤ K1 * ‖D (v - vP)‖ :=
    (hK0 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖D (v - vP)‖ ≤ ‖zL v‖ + ‖zL v - D (v - vP)‖ := by
    have := norm_sub_le (zL v) (zL v - D (v - vP))
    rwa [sub_sub_cancel] at this
  have h3 : K1 * (1 / (2 * K1) * ‖v - vP‖) = ‖v - vP‖ / 2 := by field_simp
  nlinarith [norm_nonneg (zL v - D (v - vP)), norm_nonneg (zL v)]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
