-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:31.536903+00:00
-- url     : https://prove2.me/submissions/8ebbd846-0dbe-4ec4-a0da-f6f9ead542df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Module.length (Localization.AtPrime (V.map σ))
        (LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ)) =
      Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (A ⧸ J)) := by
  have : RingHomSurjective (locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ)) := ⟨(locRingEquiv σ V).surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective
    (locQuotSemilinear σ J V) ⟨locQuotSemilinear_injective σ J V,
      locQuotSemilinear_surjective σ J V⟩)).symm
end GroundTheory.Heights₂.Heights
