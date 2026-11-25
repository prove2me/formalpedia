-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:52.567449+00:00
-- url     : https://prove2.me/submissions/1a80dcd6-2592-431a-9f43-9e3aaa2c42b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace

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
theorem _root_.solution [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by
  rw [IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]
end GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
