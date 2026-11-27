-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.isRegular_of_isArtinianRing_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:46.695386+00:00
-- url     : https://prove2.me/submissions/e5220504-a256-4b5e-8e03-82f579039bf9

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_isRegular_of_supportDim_quotient_le_zero
import Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod


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
theorem _root_.solution (h : IsCM R) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R)
    (hart : IsArtinianRing (R ⧸ Ideal.ofList xs)) : IsRegular R xs := by
  apply (isCM_iff_isCMMod.mp h).isRegular_of_supportDim_quotient_le_zero xs hxs
  · rw [Module.supportDim_self_eq_ringKrullDim]; exact hlen
  · rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _ (smul_top_eq_self' _)),
      Module.supportDim_quotient_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp inferInstance
end IsCM
end ReciprocityTheory.CA
