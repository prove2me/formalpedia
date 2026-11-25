-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:21.506674+00:00
-- url     : https://prove2.me/submissions/fc9fb63d-5051-428c-9519-3e16c854f41d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_RankPosOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
open Matrix
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have : Matrix.toLin' e = 0 := h0
  simpa using congrArg LinearMap.toMatrix' this
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
