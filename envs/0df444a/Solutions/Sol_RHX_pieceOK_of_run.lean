-- Prove2me | solution 1 for RHX.pieceOK_of_run
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:53:25.468171+00:00
-- url     : https://prove2.me/submissions/8c708bbb-18bb-4f3b-ab6a-1269c4f0c5c0

import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem pieceOK_of_run (tn tq N : ℕ) (L : Q) (P : PieceD) (S : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5) = S)
    (h : pieceOKs tn tq N L P S = true) : pieceOK tn tq N L P = true := by
  simp only [pieceOKs] at h
  simp only [pieceOK]
  rw [hrun]
  exact h

theorem boxOK_of_run (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) (S : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5) = S)
    (h : boxOKs tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi S = true) :
    boxOK tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi = true := by
  simp only [boxOKs] at h
  simp only [boxOK]
  rw [hrun]
  exact h

theorem cellOK_of_run (S : SlabD) (j : ℕ) (St : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq) (S.cell j).oc (S.N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq) 5) = St)
    (h : cellOKs S j St = true) : cellOK S j = true := by
  simp only [cellOKs] at h
  simp only [cellOK]
  rw [hrun]
  exact h

end RHX
open Arb4 Arb4.Q RHX in
theorem solution (tn tq N : ℕ) (L : Q) (P : PieceD) (S : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5) = S)
    (h : pieceOKs tn tq N L P S = true) : pieceOK tn tq N L P = true := by
  apply RHX.pieceOK_of_run <;> assumption
