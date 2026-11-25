-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.relfinrank_Pj_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:38.603982+00:00
-- url     : https://prove2.me/submissions/d1c4d9bd-0e14-466c-8a6a-ae365b337a02

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_map_Pj_one
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_map_top_Pj

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
theorem _root_.solution (j : ℕ) :
    (Pj E p (j + 1)).relfinrank (Pj E p j) = (Pj E p 1).relfinrank ⊤ := by
  rw [← map_Pj_one p j, ← map_top_Pj p j, Subfield.relfinrank_map_map]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
