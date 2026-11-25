-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.mul_pidem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:20.313485+00:00
-- url     : https://prove2.me/submissions/63834add-096e-4d11-9334-a0c752a17b94

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution (I : MaximalSpectrum A) {x : A} (hx : x ∈ I.asIdeal) : x * pidem A I = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  rw [map_mul, Pi.mul_apply, equivPi_pidem, map_zero, Pi.zero_apply]
  by_cases hL : L = I
  · subst hL
    rw [IsArtinianRing.equivPi_apply, (Ideal.Quotient.eq_zero_iff_mem).2 hx, zero_mul]
  · simp [Pi.single_apply, hL]
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
