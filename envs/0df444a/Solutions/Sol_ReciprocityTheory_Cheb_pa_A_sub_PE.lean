-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_A_sub_PE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:14.981023+00:00
-- url     : https://prove2.me/submissions/6d29c1d2-9e1e-421e-b283-0167a052b587

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_pa_log_bdd
import Theorems.Thm_ReciprocityTheory_Cheb_summable_prm_rpow
import Theorems.Thm_ReciprocityTheory_Cheb_two_le_Nrm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    |(∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) - PE E s| ≤
      2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hP := summable_prm_rpow E hs
  have h2 := summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ q : Prm E, ‖-Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)‖ ≤
      2 * ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have hN2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hN0 : (0 : ℝ) < ((Nrm q : ℕ) : ℝ) := by linarith
    have hx0 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg hN0.le _
    have hxh : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
      calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN2
    rw [Real.norm_eq_abs]
    refine (pa_log_bdd hx0 hxh).trans ?_
    have : (((Nrm q : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hg : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s)) - ((Nrm q : ℕ) : ℝ) ^ (-s)) :=
    Summable.of_norm_bounded (h2.mul_left 2) hb
  have hA : Summable (fun q : Prm E => -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))) :=
    (hg.add hP).congr (fun q => by ring)
  unfold PE
  rw [← hA.tsum_sub hP, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((h2.hasSum).mul_left 2) hb
end ReciprocityTheory.Cheb
