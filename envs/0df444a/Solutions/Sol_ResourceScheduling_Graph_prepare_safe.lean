-- Prove2me | solution 1 for ResourceScheduling.Graph.prepare_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:49.780825+00:00
-- url     : https://prove2.me/submissions/e110531b-ee9e-4831-860a-b318ff7db1c2

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_split_ones

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

private theorem cons (p : Code) (ps : List Code) (B : ℕ) (s : RAMState GraphReg)
    (hp : RAMSafe p B s) (hq : RAMSafe (block ps) B (p.eval s)) :
    RAMSafe (block (p :: ps)) B s := (ram_safe_laws p (block ps) n B s).2.1 hp hq

theorem solution (B L : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hL : s.word.length ≤ L) (hB : 9 * L * L + 3 * L + 1 ≤ B) : RAMSafe prepare B s := by
  let T := (splitOnes s.word).1
  let bits := (splitOnes s.word).2.tail
  have hsplit := (split_ones s.word).2.2.1
  have hT : T ≤ L := by dsimp [T]; omega
  have hbits : bits.length ≤ L := by simp only [bits, List.length_tail]; omega
  have hN : 3 * T ≤ B := by omega
  have hNN : (3 * T) * (3 * T) ≤ B := by
    have := Nat.mul_le_mul hT hT
    nlinarith
  let x0 := ramParseState t good s
  let x1 := x0.set n T
  let x2 := x1.set n (T + T)
  let x3 := x2.set n (3 * T)
  let x4 := x3.set size ((3 * T) * (3 * T))
  let x5 := x4.set aux bits.length
  let x6 := x5.set delta (bits.length - (3 * T) * (3 * T))
  let q : Code := .branch delta (.zero good) .skip
  let x7 := q.eval x6
  let x8 := x7.set delta ((3 * T) * (3 * T) - bits.length)
  have h0 : RAMBound B x0 := by
    have ht := ram_bound_set B s hs t T (by omega)
    have hg := ram_bound_set B (s.set t T) ht good
      (if (splitOnes s.word).2 = [] then 0 else 1) (by split <;> omega)
    exact ⟨hg.1, hbits.trans (by omega)⟩
  have h1 := ram_bound_set B x0 h0 n T (by omega)
  have h2 := ram_bound_set B x1 h1 n (T + T) (by omega)
  have h3 := ram_bound_set B x2 h2 n (3 * T) hN
  have h4 := ram_bound_set B x3 h3 size ((3 * T) * (3 * T)) hNN
  have h5 := ram_bound_set B x4 h4 aux bits.length (by omega)
  have h6 : RAMBound B x6 := ram_bound_set B x5 h5 delta _
    ((Nat.sub_le _ _).trans (by omega : bits.length ≤ B))
  have hq (x : RAMState GraphReg) (hx : RAMBound B x) : RAMSafe q B x :=
    (ram_safe_laws (.zero good) .skip delta B x).2.2
      ⟨hx, ram_bound_set B x hx good 0 (Nat.zero_le _)⟩ ⟨hx,hx⟩
  have h7 : RAMBound B x7 := (hq x6 h6).2
  have h8 : RAMBound B x8 := ram_bound_set B x7 h7 delta _ ((Nat.sub_le _ _).trans hNN)
  have he7 : x7.val size = (3 * T) * (3 * T) ∧ x7.val aux = bits.length := by
    simp [x7, q, RAMCode.eval, x6, x5, x4, RAMState.set]
    split_ifs <;> simp [RAMState.set]
  have h9 := hq x8 h8
  have hend : RAMSafe (block [q]) B x8 := cons q [] B x8 h9 ⟨h9.2,h9.2⟩
  have hsub : RAMSafe (block [.sub size aux delta, q]) B x7 :=
    cons _ _ B x7 ⟨h7, by simpa only [RAMCode.eval, he7.1, he7.2] using h8⟩
      (by simpa only [RAMCode.eval, he7.1, he7.2] using hend)
  have htail := cons q [.sub size aux delta, q] B x6 (hq x6 h6) hsub
  have hh := cons (.sub aux size delta) _ B x5 ⟨h5, h6⟩ htail
  have hh := cons (.length aux) _ B x4 ⟨h4,h5⟩ hh
  have hh := cons (.mul n n size (by decide)) _ B x3 ⟨h3,h4⟩ hh
  have hsum : T + (T + T) = 3 * T := by omega
  have hh := cons (.add t n (by decide))
    [.mul n n size (by decide), .length aux, .sub aux size delta, q, .sub size aux delta, q] B x2 ⟨h2, by
    simpa [RAMCode.eval, x2, x1, x0, ramParseState, RAMState.set, T, hsum] using h3⟩
    (by simpa [RAMCode.eval, x3, x2, x1, x0, ramParseState, RAMState.set, T, hsum] using hh)
  have hh := cons (.add t n (by decide)) _ B x1 ⟨h1,h2⟩ hh
  have hh := cons (.copy t n (by decide)) _ B x0 ⟨h0,h1⟩ hh
  exact cons (.parse t good (by decide)) _ B s ⟨hs,h0⟩ hh

#print axioms solution
