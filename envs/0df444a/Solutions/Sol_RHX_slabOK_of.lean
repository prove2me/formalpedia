-- Prove2me | solution 1 for RHX.slabOK_of
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:51:31.238911+00:00
-- url     : https://prove2.me/submissions/acf65b2d-68aa-4fb1-8597-ece1e5903b56

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

/-- `H11K.edgeRest` from its head conjuncts, the two endpoint boxes and the two final inequalities. -/
theorem edgeRest_of (E : EdgeD)
    (hh : (Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
      (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
      eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1))) = true)
    (hb0 : boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0
      E.qlo0 E.qhi0 = true)
    (hb1 : boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 = true)
    (hlo : finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo = true)
    (hhi : finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi = true) :
    H11K.edgeRest E = true := by
  simp only [H11K.edgeRest, Bool.and_eq_true] at hh ⊢
  exact ⟨⟨⟨⟨hh, hb0⟩, hb1⟩, hlo⟩, hhi⟩

/-- `Arb4.cellOK` from its conjuncts (evaluator states written out). -/
theorem cellOK_of (S : SlabD) (j : ℕ)
    (h0 : (Nat.ble 2 S.N && Nat.ble 1 (S.cell j).q && Nat.ble 1 (S.cell j).rd &&
      Nat.ble (S.cell j).b (S.cell j).a) = true)
    (hc : (let c := ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq
      let s1 := ArbEcon.Off.runO c (S.cell j).oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c (S.cell j).oc 1 s1
      ArbEcon.Off.checkCell c (S.cell j).oc 6 S.N 5 s1.acc sN.acc (S.cell j).rn (S.cell j).rd S.FN S.FD) = true)
    (hR : le (frac ((S.cell j).rn : ℤ) (S.cell j).rd) S.R = true)
    (hl : (let c := ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq
      let s1 := ArbEcon.Off.runO c (S.cell j).oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c (S.cell j).oc 1 s1
      le (ofNat sN.lhi) (mul S.L (ofNat (2 ^ 64)))) = true)
    (r1 : le S.lo (tQ (S.cell j).tn S.tq) = true)
    (r2 : le (add (npow (add (S.cell j).σQ (ofNat 11)) 2) (npow (tQ (S.cell j).tn S.tq) 2)) (npow S.U 2) = true)
    (r3 : le (qabs (sub (S.xs j) (S.cell j).σQ)) (S.cell j).w = true)
    (r4 : le (qabs (sub (S.xs (j + 1)) (S.cell j).σQ)) (S.cell j).w = true)
    (r5 : le (qabs (sub S.lo (tQ (S.cell j).tn S.tq))) (S.cell j).hh = true)
    (r6 : le (qabs (sub S.hi (tQ (S.cell j).tn S.tq))) (S.cell j).hh = true)
    (r7 : le (add (npow (S.cell j).w 2) (npow (S.cell j).hh 2)) (npow (frac ((S.cell j).rn : ℤ) (S.cell j).rd) 2) = true) :
    cellOK S j = true := by
  simp only [cellOK, Bool.and_eq_true] at h0 hc hl ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hc⟩, hR⟩, hl⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩

/-- `Arb4.slabOK` from the head and every cell. -/
theorem slabOK_of (S : SlabD) (hh : slabHeadOK S = true) (hc : ∀ j, j < S.m → cellOK S j = true) :
    slabOK S = true := by
  simp only [slabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨hh, fun j hj => hc j hj⟩

end RHX
open Arb4 Arb4.Q RHX in
theorem solution (S : SlabD) (hh : slabHeadOK S = true) (hc : ∀ j, j < S.m → cellOK S j = true) :
    slabOK S = true := by
  apply RHX.slabOK_of <;> assumption
