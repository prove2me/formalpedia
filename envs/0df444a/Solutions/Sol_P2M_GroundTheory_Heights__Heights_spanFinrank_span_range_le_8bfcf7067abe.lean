-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:00.947705+00:00
-- url     : https://prove2.me/submissions/99db7a80-87dc-45a0-9ec6-e49c6eaba14a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters

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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
  have hz : Set.range z = ((Finset.univ.image z : Finset R) : Set R) := by simp
  rw [hz, Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)
end GroundTheory.Heights₂.Heights
