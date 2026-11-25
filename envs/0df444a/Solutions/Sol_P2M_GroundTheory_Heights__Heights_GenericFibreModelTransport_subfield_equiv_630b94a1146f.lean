-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreModelTransport_subfield_equiv_630b94a1146f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:50.045795+00:00
-- url     : https://prove2.me/submissions/82ed66da-2f8f-4038-bae7-fcb70424cf3e

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
theorem _root_.solution {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by
  let g : k →+* ι.fieldRange :=
    (α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    have hy : (y : A) ∈ k.map α := hr ▸ y.2
    obtain ⟨x, hx, e⟩ := Subfield.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩
end GroundTheory.Heights₂.Heights.GenericFibreModelTransport
