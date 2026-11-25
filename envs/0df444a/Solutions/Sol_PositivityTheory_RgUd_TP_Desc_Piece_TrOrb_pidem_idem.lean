-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.pidem_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:22.605171+00:00
-- url     : https://prove2.me/submissions/3b12d176-ebf6-4b80-8306-3c29540c486b

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
theorem _root_.solution (I : MaximalSpectrum A) : IsIdempotentElem (pidem A I) := by
  have h := pidem_mul I I
  rw [if_pos rfl] at h
  exact h
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
