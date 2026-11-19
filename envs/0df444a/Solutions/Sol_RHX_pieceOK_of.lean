-- Prove2me | solution 1 for RHX.pieceOK_of
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:42:24.590454+00:00
-- url     : https://prove2.me/submissions/257d0b90-331f-4aa0-8f49-86b46322dc78

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
set_option maxRecDepth 100000
open Arb4

namespace RHX

/-- `Arb4.pieceOK` from its conjuncts, each stated with the evaluator states written out. -/
theorem pieceOK_of (tn tq N : ℕ) (L : Q) (P : PieceD)
    (h0 : (Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD) = true)
    (hc : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk) = true)
    (hg : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      geomOK tn tq L sN.lhi P) = true)
    (hG : gOK N P = true) (hr : remOK tn tq N P = true) (hb : budgetOK N L P = true) :
    pieceOK tn tq N L P = true := by
  simp only [Bool.and_eq_true] at h0
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h0
  simp only [pieceOK, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hc⟩, hg⟩, hG⟩, hr⟩, hb⟩

/-- `H11K.pieceJ` from `pieceOK` and the two radius checks. -/
theorem pieceJ_of (E : EdgeD) (j : ℕ) (hp : pieceOK E.tn E.tq E.N E.L (E.pc j) = true)
    (h1 : inRad (E.x j) (E.pc j) = true) (h2 : inRad (E.x (j + 1)) (E.pc j) = true) :
    H11K.pieceJ E j = true := by
  simp only [H11K.pieceJ, Bool.and_eq_true]
  exact ⟨⟨hp, h1⟩, h2⟩

end RHX
open Arb4 RHX in
theorem solution (tn tq N : ℕ) (L : Q) (P : PieceD)
    (h0 : (Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD) = true)
    (hc : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk) = true)
    (hg : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      geomOK tn tq L sN.lhi P) = true)
    (hG : gOK N P = true) (hr : remOK tn tq N P = true) (hb : budgetOK N L P = true) :
    pieceOK tn tq N L P = true := by
  apply RHX.pieceOK_of <;> assumption
