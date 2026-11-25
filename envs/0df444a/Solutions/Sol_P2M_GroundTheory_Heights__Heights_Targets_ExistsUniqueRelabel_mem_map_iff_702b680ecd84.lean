-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:55:07.860597+00:00
-- url     : https://prove2.me/submissions/8f5837cb-3427-423c-be2c-6b0f985214c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
