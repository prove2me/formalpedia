-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_Z_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:19.870202+00:00
-- url     : https://prove2.me/submissions/8ea14906-59d1-4371-b627-ea6dd1fae0bd

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
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
theorem _root_.solution (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by
  have h := (summable_absNorm_rpow E hs).le_tsum (⟨⊤, top_ne_bot⟩ : NZIdeal E)
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simpa [Ideal.absNorm_top] using h
end ReciprocityTheory.Cheb
