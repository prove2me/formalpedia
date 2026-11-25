-- Prove2me | solution 2 for ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:48.346476+00:00
-- url     : https://prove2.me/submissions/4c2549b3-2c20-451e-8a55-9fd7ece6b37d

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_sum_le_idealZetaR

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
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) :=
  summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ sum_le_idealZetaR E hs u
end ReciprocityTheory.Cheb
