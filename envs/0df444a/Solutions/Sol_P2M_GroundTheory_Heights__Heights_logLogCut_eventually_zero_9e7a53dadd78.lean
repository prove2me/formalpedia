-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logLogCut_eventually_zero_9e7a53dadd78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:14.415855+00:00
-- url     : https://prove2.me/submissions/983fbe6b-11ec-48bc-908d-4f01b1d4d9aa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutStep_of_one_le_8430a833c05c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cutLevel_mem_6f1a40581949


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
    (hy : ‖eval y Q‖ ^ 2 < cutLevel k) : logLogCut Q k =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Iio_mem_nhds hy)] with z hz
  have hz : ‖eval z Q‖ ^ 2 < cutLevel k := hz
  have hlt := (cutLevel_mem k).2
  unfold logLogCut
  split_ifs with h0 h1
  · rfl
  · linarith
  · have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have e1 : Real.log (‖eval z Q‖ ^ 2) < -Real.exp ((k : ℝ) + 1) :=
      (Real.log_lt_iff_lt_exp hw0).2 hz
    have e2 : (k : ℝ) + 1 < Real.log (-logAbsSq Q z) :=
      (Real.lt_log_iff_exp_lt (by rw [logAbsSq]; linarith [Real.exp_pos ((k : ℝ) + 1)])).2
        (by rw [logAbsSq]; linarith)
    apply cutStep_of_one_le
    rw [le_div_iff₀ (by positivity)]
    linarith
end GroundTheory.Heights₂.Heights
