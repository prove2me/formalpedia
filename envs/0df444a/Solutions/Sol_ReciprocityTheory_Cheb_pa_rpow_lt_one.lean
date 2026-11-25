-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_rpow_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:28.433838+00:00
-- url     : https://prove2.me/submissions/2b95c6a5-3101-4dad-93d6-080af45962fb

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 0 < s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) < 1 := by
  have h := two_le_Nrm q
  have h1 : (1 : ℝ) < ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < Nrm q)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
end ReciprocityTheory.Cheb
