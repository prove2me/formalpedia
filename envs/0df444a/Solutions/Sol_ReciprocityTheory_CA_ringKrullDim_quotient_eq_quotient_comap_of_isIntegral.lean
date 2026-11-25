-- Prove2me | solution 1 for ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:09.609822+00:00
-- url     : https://prove2.me/submissions/5aad3de1-9c18-435b-b417-ca5930af65cb

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
namespace ReciprocityTheory.CA
theorem _root_.solution {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal B) :
    ringKrullDim (B ⧸ I) = ringKrullDim (A ⧸ I.comap (algebraMap A B)) := by
  haveI : Algebra.IsIntegral (A ⧸ I.comap (algebraMap A B)) (B ⧸ I) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.quotient I
  exact ringKrullDim_eq_of_isIntegral_of_injective Ideal.algebraMap_quotient_injective
end ReciprocityTheory.CA
