-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logLogCut_eventually_one_3205ba4419f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:06.660683+00:00
-- url     : https://prove2.me/submissions/2cb1d0c1-5cd2-4601-85ee-22fefe672ffb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutStep_of_le_half_2db3d5f80c7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc

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
theorem _root_.solution {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2) :
    logLogCut Q k =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioi_mem_nhds hy)] with z hz
  have hz : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval z Q‖ ^ 2 := hz
  have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_trans (Real.exp_pos _) hz
  unfold logLogCut
  split_ifs with h0 h1
  · linarith
  · rfl
  · have hw1 : ‖eval z Q‖ ^ 2 < 1 := not_le.1 h1
    have e1 : -Real.exp (((k : ℝ) + 1) / 2) < Real.log (‖eval z Q‖ ^ 2) :=
      (Real.lt_log_iff_exp_lt hw0).2 hz
    have e0 : Real.log (‖eval z Q‖ ^ 2) < 0 := Real.log_neg hw0 hw1
    have e2 : Real.log (-logAbsSq Q z) < ((k : ℝ) + 1) / 2 :=
      (Real.log_lt_iff_lt_exp (by rw [logAbsSq]; linarith)).2 (by rw [logAbsSq]; linarith)
    apply cutStep_of_le_half
    rw [div_le_iff₀ (by positivity)]
    linarith
end GroundTheory.Heights₂.Heights
