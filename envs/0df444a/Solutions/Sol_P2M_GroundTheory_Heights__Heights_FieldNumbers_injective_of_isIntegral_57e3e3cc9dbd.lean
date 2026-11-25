-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:00.119957+00:00
-- url     : https://prove2.me/submissions/b9204f0b-3cbd-45a3-9c8b-b334f536d5b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Polynomial
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {B B' Ω : Type*} [CommRing B] [Nontrivial B] [CommRing B']
    [IsDomain B'] [CommRing Ω] [Algebra B B'] [Algebra.IsIntegral B B'] (ψ : B' →+* Ω)
    (h : Function.Injective (ψ.comp (algebraMap B B'))) : Function.Injective ψ := by
  have : RingHom.ker ψ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := B)
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp h
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr this
end GroundTheory.Heights₂.Heights.FieldNumbers
