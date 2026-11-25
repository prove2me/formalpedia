-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_map_mk_lt_4b93d3dede51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:34.371984+00:00
-- url     : https://prove2.me/submissions/2fe9d83d-63e1-4636-b08d-1a2b2c36ae43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe

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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution {p a b : Ideal R} (ha : p ≤ a) (hab : a < b) :
    a.map (Ideal.Quotient.mk p) < b.map (Ideal.Quotient.mk p) := by
  have key : ∀ c : Ideal R, p ≤ c →
      (c.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = c := by
    intro c hc
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hc
  refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
  rw [← key a ha, ← key b (ha.trans hab.le), h]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
