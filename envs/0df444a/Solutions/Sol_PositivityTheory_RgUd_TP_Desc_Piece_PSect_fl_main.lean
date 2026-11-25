-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:26.668527+00:00
-- url     : https://prove2.me/submissions/f1ce20d2-5fb9-4bfe-94dc-cf1105786a5d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_greedy

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
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∃ n, finrank F E = p ^ n ∧ ∃ α : Fin n → E, adjoin F (Set.range α) = ⊤ := by
  obtain ⟨n, hn, α, hα⟩ := fl_greedy p h _ ⊥ rfl
  refine ⟨n, ?_, α, ?_⟩
  · rw [← hn, relfinrank_bot_left, finrank_top']
  · rwa [bot_sup_eq] at hα
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
