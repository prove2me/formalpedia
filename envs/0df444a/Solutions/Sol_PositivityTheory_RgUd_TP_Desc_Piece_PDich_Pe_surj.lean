-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:32.38248+00:00
-- url     : https://prove2.me/submissions/2728075e-e5f5-438b-a6b1-9db5d3482190

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
theorem _root_.solution (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := LinearMap.surjective_rangeRestrict _
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
