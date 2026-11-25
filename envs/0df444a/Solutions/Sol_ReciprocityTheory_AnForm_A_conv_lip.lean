-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.conv_lip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:36.150328+00:00
-- url     : https://prove2.me/submissions/17b0fa73-58e9-4721-a6b0-91491810bc7e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_lt_of_scaled_ne_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_scaled
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_scaled

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} {L : NNReal} (hg : LipschitzWith L g)
    (z : Fin D → ℂ) : ‖(∫ w, ρ.scaled ε w • g (z - w)) - g z‖ ≤ L * ε := by
  have hc : Continuous fun w => ρ.scaled ε w • g (z - w) :=
    (scaled_contDiff ρ ε).continuous.smul (hg.continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable fun w => ρ.scaled ε w • g (z - w) :=
    hc.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε).smul_right
  have hi2 : Integrable fun w => ρ.scaled ε w • g z := (integrable_scaled ρ hε).smul_const _
  have e1 : g z = ∫ w, ρ.scaled ε w • g z := by
    rw [integral_smul_const, integral_scaled ρ hε, one_smul]
  rw [e1, ← integral_sub hi hi2]
  have hb : Integrable fun w => ρ.scaled ε w * (L * ε) := (integrable_scaled ρ hε).mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun w => ?_)).trans ?_
  · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (scaled_nonneg ρ hε w)]
    by_cases hw : ρ.scaled ε w = 0
    · simp [hw]
    · refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε w)
      have h1 := hg.dist_le_mul (z - w) z
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h1
      calc ‖g (z - w) - g z‖ ≤ L * ‖w‖ := h1
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (norm_lt_of_scaled_ne_zero ρ hε hw).le L.coe_nonneg
  · rw [integral_mul_const, integral_scaled ρ hε, one_mul]
end ReciprocityTheory.AnForm.A
