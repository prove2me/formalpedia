-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.quotient_ofList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:17:45.333678+00:00
-- url     : https://prove2.me/submissions/68a70e2b-db97-4d22-b39c-ed64a69cfff8

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotient_ofList
import Theorems.Thm_ReciprocityTheory_CA_isCMMod_congr
import Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod
import Theorems.Thm_ReciprocityTheory_CA_isCM_quotient_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution (h : IsCM R) {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular R rs) [IsLocalRing (R ⧸ Ideal.ofList rs)] :
    IsCM (R ⧸ Ideal.ofList rs) := by
  haveI : IsNoetherianRing R := h.1
  have h1 := (isCM_iff_isCMMod.mp h).quotient_ofList hrs reg
  exact (isCM_quotient_iff _).mpr
    ((isCMMod_congr (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _))).mp h1)
end IsCM
end ReciprocityTheory.CA
