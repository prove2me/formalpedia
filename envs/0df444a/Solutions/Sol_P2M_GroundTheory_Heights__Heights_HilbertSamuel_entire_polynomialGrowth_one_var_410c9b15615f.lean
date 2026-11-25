-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_entire_polynomialGrowth_one_var_410c9b15615f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:23.26618+00:00
-- url     : https://prove2.me/submissions/6f6b22a6-1a69-43db-9e54-55af3df543cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PEntirePolynomialGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Metric
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (M : ℕ) : ∀ (g : ℂ → ℂ) (C : ℝ), Differentiable ℂ g →
    (∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ M) →
    ∃ q : Polynomial ℂ, q.natDegree ≤ M ∧ ∀ z, g z = q.eval z := by
  induction M with
  | zero =>
    intro g C hg hb
    refine ⟨Polynomial.C (g 0), by simp, fun z => ?_⟩
    rw [Polynomial.eval_C]
    refine hg.apply_eq_apply_of_bounded ?_ z 0
    refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa using hb w
  | succ M ih =>
    intro g C hg hb
    set h := dslope g 0 with hh
    have hdiff : Differentiable ℂ h := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hg.differentiableOn
    obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ B :=
      (isCompact_closedBall 0 1).exists_bound_of_continuousOn hdiff.continuous.continuousOn
    have hrep : ∀ z, g z = g 0 + z * h z := fun z => by
      have := sub_smul_dslope g 0 z
      rw [smul_eq_mul, sub_zero] at this
      linear_combination -this
    set C' := max C 0 with hC'def
    have hC' : 0 ≤ C' := le_max_right _ _
    have hb' : ∀ z, ‖g z‖ ≤ C' * (1 + ‖z‖) ^ (M + 1) := fun z =>
      (hb z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hgrowth : ∀ z, ‖h z‖ ≤ (max B 0 + 2 * C' + ‖g 0‖) * (1 + ‖z‖) ^ M := by
      intro z
      have hg0 := norm_nonneg (g 0)
      have hBm := le_max_left B 0
      have hB0 := le_max_right B 0
      rcases le_or_gt ‖z‖ 1 with hz | hz
      · have h1 : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have := hB z (by simpa using hz)
        nlinarith
      · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
        have hhz : h z = (g z - g 0) / z := by
          rw [hh, dslope_of_ne _ hz0, slope_def_field, sub_zero]
        rw [hhz, norm_div, div_le_iff₀ (by positivity)]
        have e1 := norm_sub_le (g z) (g 0)
        have e2 := hb' z
        have hP : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg z])
        have hs : (1 + ‖z‖) ^ (M + 1) = (1 + ‖z‖) ^ M * (1 + ‖z‖) := pow_succ _ _
        rw [hs] at e2
        have k1 : 0 ≤ C' * (1 + ‖z‖) ^ M * (‖z‖ - 1) :=
          mul_nonneg (mul_nonneg hC' (by positivity)) (by linarith)
        have k2 : 0 ≤ ‖g 0‖ * ((1 + ‖z‖) ^ M * ‖z‖ - 1) :=
          mul_nonneg hg0 (by nlinarith)
        have k3 : 0 ≤ max B 0 * (1 + ‖z‖) ^ M * ‖z‖ := by positivity
        nlinarith
    obtain ⟨q, hqdeg, hq⟩ := ih h (max B 0 + 2 * C' + ‖g 0‖) hdiff hgrowth
    refine ⟨Polynomial.C (g 0) + Polynomial.X * q, ?_, fun z => ?_⟩
    · calc (Polynomial.C (g 0) + Polynomial.X * q).natDegree
          ≤ max (Polynomial.C (g 0)).natDegree (Polynomial.X * q).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ M + 1 := by
            refine max_le (by simp) (Polynomial.natDegree_mul_le.trans ?_)
            have := Polynomial.natDegree_X_le (R := ℂ)
            omega
    · rw [hrep z, hq z]; simp
end GroundTheory.Heights₂.Heights.HilbertSamuel
