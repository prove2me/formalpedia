-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.map_Pj_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:03.831116+00:00
-- url     : https://prove2.me/submissions/78773da7-0919-4d97-bade-bf4952f83be8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_comp_iterateFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial IntermediateField
variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution (j : ℕ) : (Pj E p 1).map (iterateFrobenius E p j) = Pj E p (j + 1) := by
  rw [Pj, RingHom.map_fieldRange, comp_iterateFrobenius, Pj]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
