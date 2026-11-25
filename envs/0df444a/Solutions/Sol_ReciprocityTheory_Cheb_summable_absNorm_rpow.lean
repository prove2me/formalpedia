-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_absNorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:43.275815+00:00
-- url     : https://prove2.me/submissions/f843274a-ac9d-48cb-a857-2dc6158ce3c5

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal

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
    Summable (fun a : NZIdeal E => ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)) :=
  (summable_absNorm_rpow_ideal E hs).subtype _
end ReciprocityTheory.Cheb
