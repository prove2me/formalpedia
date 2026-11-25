-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_map_2b7a12218846
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:50.463906+00:00
-- url     : https://prove2.me/submissions/adcdb980-353a-42a2-a0ac-8dbc12e30770

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericFibProps

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
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.NumbersDVR
