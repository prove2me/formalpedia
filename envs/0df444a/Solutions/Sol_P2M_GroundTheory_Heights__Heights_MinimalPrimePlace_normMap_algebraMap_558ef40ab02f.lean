-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:42:48.085848+00:00
-- url     : https://prove2.me/submissions/8e726813-d918-441f-9c39-f325a21b9ced

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace

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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A) :
    normMap π hker (algebraMap A (integralClosure A (FractionRing A)) a) =
      algebraMap B (integralClosure B (FractionRing B)) (π a) :=
  Subtype.ext (IsLocalization.map_eq (S := FractionRing A) (Q := FractionRing B) (g := π)
    (hy := le_comap_nonZeroDivisors π hker) (x := a))
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
