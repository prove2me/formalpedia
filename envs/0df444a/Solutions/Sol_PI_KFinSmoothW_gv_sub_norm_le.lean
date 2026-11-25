-- Prove2me | solution 1 for PI.KFinSmoothW.gv_sub_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:45.485503+00:00
-- url     : https://prove2.me/submissions/90b7dcd5-491b-4e53-83fa-c6cce04f6099

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
import Theorems.Thm_PI_KFinSmoothW_umat_mem_UJset
import Theorems.Thm_PI_KFinSmoothW_cont_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.KFinSmoothW
theorem _root_.solution [CompleteSpace H] {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hτ : IsURepOn (UJset ε) τ)
    (Φr : Matrix (Fin n) (Fin n) ℂ → ℝ) (hΦc : Continuous Φr) (hΦ0 : ∀ x, 0 ≤ Φr x)
    (hint : Integrable (fun h : UJ ε => Φr (umat h)) (muG ε))
    (h1 : ∫ h, Φr (umat h) ∂(muG ε) = 1) (u : H) (δ : ℝ)
    (hsupp : ∀ h : UJ ε, Φr (umat h) ≠ 0 → ‖τ (umat h) u - u‖ ≤ δ) :
    ‖gv ε τ (fun x => (Φr x : ℂ)) u - u‖ ≤ δ := by
  have hc := cont_orbit hτ u
  have hI1 : Integrable (fun h : UJ ε => Φr (umat h) • τ (umat h) u) (muG ε) := by
    refine Integrable.mono' (hint.mul_const ‖u‖) ?_ ?_
    · exact ((hΦc.comp (continuous_coeMatrix ε)).smul hc).aestronglyMeasurable
    · filter_upwards with h
      rw [norm_smul, hτ.2.1 _ (umat_mem_UJset h), Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
  have hI2 : Integrable (fun h : UJ ε => Φr (umat h) • u) (muG ε) := hint.smul_const u
  have hgv : gv ε τ (fun x => (Φr x : ℂ)) u = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) := by
    unfold gv
    congr 1
  have hu : ∫ h, Φr (umat h) • u ∂(muG ε) = u := by
    rw [integral_smul_const, h1, one_smul]
  have hdiff : ∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε) =
      ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) - u := by
    simp_rw [smul_sub]
    rw [integral_sub hI1 hI2, hu]
  rw [hgv, ← hdiff]
  calc ‖∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε)‖
      ≤ ∫ h, Φr (umat h) * δ ∂(muG ε) := by
        refine norm_integral_le_of_norm_le (hint.mul_const δ) ?_
        filter_upwards with h
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
        by_cases hz : Φr (umat h) = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hsupp h hz) (hΦ0 _)
    _ = δ := by rw [integral_mul_const, h1, one_mul]
end PI.KFinSmoothW
