-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.finrank_piece_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:56.56957+00:00
-- url     : https://prove2.me/submissions/1fa19eea-bc61-4788-83ab-39a211340b8c

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
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {N : ℕ}
variable (ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k)
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution (e : A) : finrank k (piece (Rep ρ) e) = (ρ e).rank := by
  have hs : ((piece (Rep ρ) e).restrictScalars k : Submodule k (Fin N → k)) =
      LinearMap.range (ρ e).mulVecLin := by
    ext v
    simp only [Submodule.restrictScalars_mem, piece, LinearMap.mem_range, LinearMap.lsmul_apply,
      Matrix.mulVecLin_apply]
    rfl
  rw [Matrix.rank, ← hs]
  rfl
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
