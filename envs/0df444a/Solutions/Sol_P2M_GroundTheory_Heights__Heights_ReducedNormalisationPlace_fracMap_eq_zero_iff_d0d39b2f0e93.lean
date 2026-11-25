-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:37.280541+00:00
-- url     : https://prove2.me/submissions/6038a3e3-12c7-429b-b01e-745c99fb2ffd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
open GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
theorem _root_.solution {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  rw [fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]
end GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
