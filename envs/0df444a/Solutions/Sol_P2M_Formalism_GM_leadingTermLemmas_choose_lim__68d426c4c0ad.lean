-- Prove2me | solution 1 for P2M_Formalism_GM_leadingTermLemmas_choose_lim__68d426c4c0ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:15.04502+00:00
-- url     : https://prove2.me/submissions/6909d4b4-0876-44d5-9a0f-1b7354cbeac8

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_choose_lim
import Theorems.Thm_Formalism_GM_leadingTermLemmas_inv_pow_lim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (S j d : ℕ) (hjd : j ≤ d) :
    Tendsto (fun n : ℕ => ((n + j - S).choose j : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (if j = d then 1 / (d.factorial : ℝ) else 0)) := by
  by_cases h : j = d
  · subst h; rw [if_pos rfl]; exact choose_lim j S j
  · rw [if_neg h]
    have h1 := (choose_lim j S j).mul (inv_pow_lim (d - j) (by omega))
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [show d = j + (d - j) by omega, pow_add]
    field_simp
    rw [Nat.add_sub_cancel_left]
end Formalism.GM.leadingTermLemmas
