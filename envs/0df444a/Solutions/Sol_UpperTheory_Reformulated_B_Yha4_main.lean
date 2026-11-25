-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yha4.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:28.924094+00:00
-- url     : https://prove2.me/submissions/fcb74d46-2117-48cf-93a1-e3f0f10e7ee5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace YhaHelp
open MeasureTheory Set Real
private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)
end YhaHelp
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yha4
theorem _root_.solution :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
end UpperTheory.Reformulated.B.Yha4
