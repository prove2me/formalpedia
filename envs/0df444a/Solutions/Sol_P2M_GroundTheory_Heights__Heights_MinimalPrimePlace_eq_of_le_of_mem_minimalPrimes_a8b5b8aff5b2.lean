-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:59.200856+00:00
-- url     : https://prove2.me/submissions/3f890496-4964-4ef2-b1d3-5130ba932746

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
theorem _root_.solution {q q' : Ideal A} (hq : q ∈ minimalPrimes A) (hq' : q' ∈ minimalPrimes A)
    (h : q ≤ q') : q = q' :=
  le_antisymm h (hq'.2 hq.1 h)
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
