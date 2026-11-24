-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:41.089927+00:00
-- url     : https://prove2.me/submissions/bbe82beb-ef21-46dc-bdc7-72599d74292f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by
  intro d hd
  rw [coeff_map] at hd
  apply hp
  intro h0
  exact hd (by rw [h0, map_zero])
end GroundTheory.Heights₂.Heights.NumbersDVR
