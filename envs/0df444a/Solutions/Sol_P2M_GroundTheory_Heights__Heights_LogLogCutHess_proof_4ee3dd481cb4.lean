-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogLogCutHess_proof_4ee3dd481cb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:41.995631+00:00
-- url     : https://prove2.me/submissions/8d2da8bb-a638-41d9-9454-19af7ee28bff

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHess
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeWeight_nonneg_09efcdebf9fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogStep_deriv2_bound_27528040605c
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_log_norm
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_log_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LogLogCutHess
theorem _root_.solution (hC : HessCCompPluri.Statement) : LogLogCutHess.Statement := by
  obtain ⟨K, hK0, hK⟩ := logLogStep_deriv2_bound
  refine ⟨K, hK0, fun m Q k y => ?_⟩
  have hc : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnn : 0 ≤ K / ((k : ℝ) + 1) * tubeWeight Q y :=
    mul_nonneg (div_nonneg hK0 (by linarith)) (tubeWeight_nonneg Q y)
  have hconst : ∀ c : ℝ, logLogCut Q k =ᶠ[𝓝 y] (fun _ => c) → ∃ a b : ℝ,
      |a| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧ |b| ≤ K / ((k : ℝ) + 1) * tubeWeight Q y ∧
      hessC (logLogCut Q k) y = (a : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y ∧
      hessC (fun z => logLogCut Q k z ^ 2 / 2) y = (b : ℂ) • hessC (fun z => logAbsSq Q z ^ 2 / 2) y := by
    intro c hev
    obtain ⟨e1, e2⟩ := hessC_of_eventually_const hev
    exact ⟨0, 0, by simpa using hnn, by simpa using hnn, by simp [e1], by simp [e2]⟩
  by_cases h1 : ‖eval y Q‖ ^ 2 < cutLevel k
  · exact hconst 0 (logLogCut_eventually_zero Q k h1)
  by_cases h2 : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2
  · exact hconst 1 (logLogCut_eventually_one Q k h2)
  have hw0 : 0 < ‖eval y Q‖ ^ 2 := lt_of_lt_of_le (cutLevel_mem k).1 (not_lt.1 h1)
  have hw1 : ‖eval y Q‖ ^ 2 < 1 :=
    lt_of_le_of_lt (not_lt.1 h2) (Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _)))
  have hLy : logAbsSq Q y ≤ -1 := by
    have e1 : logAbsSq Q y ≤ -Real.exp (((k : ℝ) + 1) / 2) := (Real.log_le_iff_le_exp hw0).2 (not_lt.1 h2)
    have e2 : 1 ≤ Real.exp (((k : ℝ) + 1) / 2) := Real.one_le_exp (by positivity)
    linarith
  have htw : tubeWeight Q y = (logAbsSq Q y ^ 2)⁻¹ := if_pos hLy
  have hg : AnalyticAt ℂ (fun z => eval z Q) y := AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)
  have hgy : eval y Q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw0
    norm_num at hw0
  have hLcd : ContDiffAt ℝ 2 (logAbsSq Q) y :=
    (((contDiff_norm_sq ℝ).contDiffAt).comp y (hg.contDiffAt.restrict_scalars ℝ)).log hw0.ne'
  have hlcd : ContDiffAt ℝ 2 (fun z => Real.log ‖eval z Q‖) y :=
    ((contDiffAt_norm ℝ hgy).comp y (hg.contDiffAt.restrict_scalars ℝ)).log (norm_ne_zero_iff.2 hgy)
  have hLpl : hessC (logAbsSq Q) y = 0 := by
    have e : logAbsSq Q = fun z => Real.log ‖eval z Q‖ + Real.log ‖eval z Q‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      push_cast
      ring
    rw [e]
    exact (hessC_add_log_norm _ (fun z => eval z Q) y hlcd hg hgy).trans (hessC_log_norm _ y hg hgy)
  obtain ⟨hFcd, hHcd, hF2, hH2⟩ := hK ((k : ℝ) + 1) hc (logAbsSq Q y) (by linarith)
  have hev := logLogCut_eventually_step Q k hw0 hw1
  have hevsq : (fun z => logLogCut Q k z ^ 2 / 2) =ᶠ[𝓝 y]
      fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) ^ 2 / 2 := by
    filter_upwards [hev] with z hz
    rw [hz]
  have eF := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1))) (logAbsSq Q) y hFcd hLcd hLpl
  have eH := hC m (fun x => cutStep (Real.log (-x) / ((k : ℝ) + 1)) ^ 2 / 2) (logAbsSq Q) y hHcd hLcd hLpl
  rw [← hessC_congr' hev] at eF
  rw [← hessC_congr' hevsq] at eH
  refine ⟨_, _, ?_, ?_, eF, eH⟩
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hF2
  · rw [htw, ← div_eq_mul_inv, div_div]; exact hH2
end LogLogCutHess
end GroundTheory.Heights₂.Heights
