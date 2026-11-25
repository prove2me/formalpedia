-- Prove2me | solution 1 for ReciprocityTheory.CA.height_eq_add_of_isCM_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:59.546821+00:00
-- url     : https://prove2.me/submissions/62b5c274-3220-4789-bd27-f9f0782f87de

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_localization_quotient_eq_height


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
theorem _root_.solution {S : Type*} [CommRing S] (𝔑 𝔔 : Ideal S) [𝔑.IsPrime]
    [𝔔.IsPrime] (h : IsCM (Localization.AtPrime 𝔑)) (hle : 𝔔 ≤ 𝔑) :
    𝔑.height = 𝔔.height + (𝔑.map (Ideal.Quotient.mk 𝔔)).height := by
  have hdisj : Disjoint (𝔑.primeCompl : Set S) 𝔔 := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (hle hxQ)
  haveI : (𝔔.map (algebraMap S (Localization.AtPrime 𝔑))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔑.primeCompl _ 𝔔 ‹_› hdisj
  have h1 := h.height_add_ringKrullDim_quotient (𝔔.map (algebraMap S (Localization.AtPrime 𝔑)))
  rw [IsLocalization.height_map_of_disjoint 𝔑.primeCompl 𝔔 hdisj,
    ringKrullDim_localization_quotient_eq_height 𝔔 𝔑 hle,
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑] at h1
  exact_mod_cast h1.symm
end ReciprocityTheory.CA
