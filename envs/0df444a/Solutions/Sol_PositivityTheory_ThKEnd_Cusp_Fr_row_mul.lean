-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.row_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:38.399194+00:00
-- url     : https://prove2.me/submissions/d936a9c6-9f43-4845-a0d5-c217daeccec8

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
open PositivityTheory.ThKEnd.Cusp.Fr
variable (h : Fr c J u u')
include h
namespace PositivityTheory.ThKEnd.Cusp.Fr
theorem _root_.solution {s s' : Matrix n n R} (hs : Adj c J s s') {g : Matrix ι ι R} (e : s' * u = u * g) :
    row c J u * s = (g.map c)ᵀ * row c J u := by
  rw [row, ← transpose_transpose s, ← transpose_mul, ← Matrix.mul_assoc, hs, Matrix.mul_assoc, ← Matrix.map_mul, e,
    Matrix.map_mul, ← Matrix.mul_assoc, transpose_mul]
end PositivityTheory.ThKEnd.Cusp.Fr
