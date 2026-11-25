-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.relfinrank_Pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:37.811349+00:00
-- url     : https://prove2.me/submissions/d6a4111f-0061-4d00-8f2b-687a52052c7f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_Pj_zero
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_Pj_succ_le
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_relfinrank_Pj_succ

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
    (Pj E p j).relfinrank ⊤ = ((Pj E p 1).relfinrank ⊤) ^ j := by
  induction j with
  | zero => rw [pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
  | succ j ih =>
    rw [← Subfield.relfinrank_mul_relfinrank (Pj_succ_le p j) le_top, relfinrank_Pj_succ, ih,
      pow_succ']
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
