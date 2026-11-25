-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_of_map_coeff_48b37feba469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:21.613152+00:00
-- url     : https://prove2.me/submissions/ea9302ba-5723-4ad4-9452-a57727f81c59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank

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
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f) {w : σ → M}
    {g : MvPolynomial σ R} {b : M} (h : IsWeightedHomogeneous w (map f g) b) :
    IsWeightedHomogeneous w g b := by
  intro d hd
  apply h
  rw [coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd
end GroundTheory.Heights₂.Heights.NumbersDVR
