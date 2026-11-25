-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ord_zero_eq_top_of_dvr_6748b86cf7d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:35:45.211038+00:00
-- url     : https://prove2.me/submissions/e5294ff2-e3fd-430a-b925-64e440164ef1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder

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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by
  rw [Ring.ord_zero]
  by_contra h
  have hfin := Module.length_ne_top_iff.1 h
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)
end GroundTheory.Heights₂.Heights
