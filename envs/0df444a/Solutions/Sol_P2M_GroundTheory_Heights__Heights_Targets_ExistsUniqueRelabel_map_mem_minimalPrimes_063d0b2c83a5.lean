-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_063d0b2c83a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:34.804985+00:00
-- url     : https://prove2.me/submissions/d942fafc-9668-4fd8-ad04-bfd38082c96d

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
theorem _root_.solution {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
  exact Ideal.minimalPrimes_comap_of_surjective (f := (φ.symm : R' →+* R)) φ.symm.surjective h
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
