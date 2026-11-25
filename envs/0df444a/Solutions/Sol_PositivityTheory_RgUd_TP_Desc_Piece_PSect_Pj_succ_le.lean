-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.Pj_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:30.105831+00:00
-- url     : https://prove2.me/submissions/e38f023e-5e8a-4f8d-9b05-73d16a7d7b6c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pj

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
theorem _root_.solution (j : ℕ) : Pj E p (j + 1) ≤ Pj E p j := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
  exact (mem_Pj p).2 ⟨x ^ p, by rw [← pow_mul, pow_succ']⟩
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
