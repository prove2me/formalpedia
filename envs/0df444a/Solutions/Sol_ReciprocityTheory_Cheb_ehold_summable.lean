-- Prove2me | solution 1 for ReciprocityTheory.Cheb.ehold_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:13.276039+00:00
-- url     : https://prove2.me/submissions/7ce628a9-1180-427d-bb35-2b51337f659d

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeCont
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Theorems.Thm_ReciprocityTheory_Cheb_ehold_norm_cpow
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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : NZIdeal E → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ‖f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))‖) := by
  refine (summable_absNorm_rpow E hs).of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
  rw [norm_mul, ehold_norm_cpow _ hs]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf a)
end ReciprocityTheory.Cheb
