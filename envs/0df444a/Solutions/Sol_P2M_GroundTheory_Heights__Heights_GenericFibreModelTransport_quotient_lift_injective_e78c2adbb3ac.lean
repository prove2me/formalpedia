-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_quotient_lift_injective_e78c2adbb3ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:48.029394+00:00
-- url     : https://prove2.me/submissions/1a2bb52f-6acf-4cbe-8267-82d4c8bc31ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_QuotientLiftInjective

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
open GroundTheory.Heights₂.Heights.GenericFibreModelTransport
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.GenericFibreModelTransport
theorem _root_.solution {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.lift_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h]
  exact ha
end GroundTheory.Heights₂.Heights.GenericFibreModelTransport
