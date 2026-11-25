-- Prove2me | solution 1 for P2M_PositivityTheory_RgUd_TP_Desc_Piece_PDich_toMatrix__mulVec__345f3a5cd0bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:39.79842+00:00
-- url     : https://prove2.me/submissions/f8efd9a3-1107-4909-88d0-c2e86303b410

import Mathlib
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
