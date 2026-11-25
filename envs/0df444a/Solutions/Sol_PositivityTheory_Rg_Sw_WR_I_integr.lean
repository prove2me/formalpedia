-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.integr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:57.687859+00:00
-- url     : https://prove2.me/submissions/c8bb9aa6-f6da-48c3-815f-5215d39960c0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_dP_ge
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_continuous_dP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_norm_sq_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution : Integr := by
  intro n
  refine ⟨⟨1, one_pos, fun y => by simpa using dP_ge y⟩, fun σ hσ => ?_⟩
  have hfin : (Module.finrank ℝ (E n) : ℝ) = (n : ℝ) ^ 2 := by
    have h : Module.finrank ℝ (Fin n → Fin n → ℝ) = n * n := by
      rw [Module.finrank_pi_fintype]
      simp
    change ((Module.finrank ℝ (Fin n → Fin n → ℝ) : ℕ) : ℝ) = (n : ℝ) ^ 2
    rw [h]
    push_cast
    ring
  have hr : (Module.finrank ℝ (E n) : ℝ) < 2 * σ := by rw [hfin]; linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (E n))) hr
  have hσ0 : 0 ≤ σ := by nlinarith [sq_nonneg (n : ℝ)]
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (continuous_dP.rpow_const fun y => Or.inl (dP_pos y).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dP_pos y).le _)]
    have h1 : 1 + ‖y‖ ^ 2 ≤ dP y := by linarith [norm_sq_le_sum y, dP_ge y]
    have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
    rw [show -(2 * σ) / 2 = -σ by ring]
    exact Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
end PositivityTheory.Rg.Sw.WR.I
