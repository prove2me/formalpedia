-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pe_log_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:16.359486+00:00
-- url     : https://prove2.me/submissions/a29ee776-0d5f-432c-9a14-db0bc7b04a7e

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_real_euler
import Theorems.Thm_ReciprocityTheory_Cheb_pa_A_sub_PE
import Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_ge_one
import Theorems.Thm_ReciprocityTheory_Cheb_pa_g_bdd

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
theorem _root_.solution : faceMap_castSucc_comp_eq_succ := by
  intro E _ _
  obtain ⟨m, M, hm, hbd⟩ := pa_g_bdd E
  refine ⟨2 * ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) + (|Real.log m| + |Real.log M|), fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hbd s hs
  have hs1 : 1 < s := hs.1
  have hAP := pa_A_sub_PE E hs1
  have hZ := pa_Z_ge_one E hs1
  have he := real_euler E hs1
  set A := ∑' q : Prm E, -Real.log (1 - ((Nrm q : ℕ) : ℝ) ^ (-s))
  set Z := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)
  have hAZ : A = Real.log Z := by rw [← he, Real.log_exp]
  have hg0 : 0 < (s - 1) * Z := lt_of_lt_of_le hm h1
  have hlog : A - Real.log (1 / (s - 1)) = Real.log ((s - 1) * Z) := by
    rw [hAZ, one_div, Real.log_inv, Real.log_mul (by linarith) (by linarith)]
    ring
  have hl1 : Real.log m ≤ Real.log ((s - 1) * Z) := Real.log_le_log hm h1
  have hl2 : Real.log ((s - 1) * Z) ≤ Real.log M := Real.log_le_log hg0 h2
  have hb : |Real.log ((s - 1) * Z)| ≤ |Real.log m| + |Real.log M| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)],
      by linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]⟩
  have e : PE E s - Real.log (1 / (s - 1)) = -(A - PE E s) + (A - Real.log (1 / (s - 1))) := by ring
  rw [e, hlog]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith
end ReciprocityTheory.Cheb
