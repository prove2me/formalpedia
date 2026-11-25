-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_one_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:41.126905+00:00
-- url     : https://prove2.me/submissions/dfc6a8f1-dc2f-4f47-8b30-70f87f311221

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : NZIdeal E) :
    (1 : ℝ) ≤ ((Ideal.absNorm a.1 : ℕ) : ℝ) := by
  have h : Ideal.absNorm a.1 ≠ 0 := by
    intro h0
    exact a.2 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
end ReciprocityTheory.Cheb
