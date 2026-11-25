-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_Z_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:12.56185+00:00
-- url     : https://prove2.me/submissions/f13bfdab-4432-4238-b8e0-af18d588d3b6

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_pa_one_le_absNorm
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow


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
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s t : ℝ} (ht : 1 < t) (hts : t ≤ s) :
    ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤
      ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t) :=
  Summable.tsum_le_tsum (fun a => Real.rpow_le_rpow_of_exponent_le (pa_one_le_absNorm a) (by linarith))
    (summable_absNorm_rpow E (lt_of_lt_of_le ht hts)) (summable_absNorm_rpow E ht)
end ReciprocityTheory.Cheb
