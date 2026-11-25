-- Prove2me | solution 1 for PositivityTheory.ThKOwn.family_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:45.511801+00:00
-- url     : https://prove2.me/submissions/c0850773-bc00-4bde-b95c-37e567273267

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
import Theorems.Thm_PositivityTheory_ThKOwn_expo_tg
import Theorems.Thm_PositivityTheory_ThKOwn_expo_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open Filter Topology Complex GlobalTheory.CompanionTheory.OM.SchDiff GlobalTheory.CompanionTheory.OM.GaussSch
open scoped SchwartzMap ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (L : V →L[ℝ] ℝ) {Q : V → ℂ} {w : ℝ}
namespace PositivityTheory.ThKOwn
theorem _root_.solution (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) (z : ℂ) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ expo L Q) (p, x)‖ ≤ C := by
  obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_cexp_comp_le (expo_tg L hQ) n
  set R : ℝ := ‖z‖ + 1
  set B : ℝ := (R * ‖L‖) ^ 2 / (2 * w)
  refine ⟨C * (1 + R) ^ j * Real.exp B * Real.exp ((k + j : ℕ) ^ 2 / (4 * (w / 2))), fun p hp x => ?_⟩
  have hp' : ‖p‖ ≤ R := by
    have := norm_add_le z (p - z)
    rw [add_sub_cancel] at this
    linarith
  have hR : 0 ≤ R := (norm_nonneg p).trans hp'
  have h1 : 1 + ‖(p, x)‖ ≤ (1 + R) * (1 + ‖x‖) := by
    have : ‖(p, x)‖ ≤ ‖p‖ + ‖x‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by simp)
    nlinarith [mul_nonneg hR (norm_nonneg x)]
  have h2 := Real.exp_le_exp.2 (expo_re L hw hre hp' x)
  have h3 := one_add_pow_mul_exp_le (half_pos hw) (norm_nonneg x) (k + j)
  have h4 : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  calc _ ≤ (1 + ‖x‖) ^ k * (C * ((1 + R) * (1 + ‖x‖)) ^ j * Real.exp (B + -(w / 2) * ‖x‖ ^ 2)) := by
        gcongr
        exact (hb _).trans (by gcongr)
    _ = C * (1 + R) ^ j * Real.exp B * ((1 + ‖x‖) ^ (k + j) * Real.exp (-(w / 2) * ‖x‖ ^ 2)) := by
        rw [Real.exp_add, mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr
end PositivityTheory.ThKOwn
