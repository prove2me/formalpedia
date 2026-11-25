-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:24.281572+00:00
-- url     : https://prove2.me/submissions/0f049294-a2b5-4918-b684-4055d486f5b7

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
variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := rfl
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
