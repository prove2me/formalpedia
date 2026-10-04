-- Prove2me | solution 1 for ResourceScheduling.Graph.validate_cell_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:19.566618+00:00
-- url     : https://prove2.me/submissions/bb91682e-1187-478b-9582-a3bdb16e5608

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_read_safe
import Theorems.Thm_ResourceScheduling_Graph_read_eval

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

private theorem two (p q : Code) (B : ℕ) (s : RAMState GraphReg)
    (hp : RAMSafe p B s) (hq : RAMSafe q B (p.eval s)) : RAMSafe (block [p,q]) B s := by
  exact (ram_safe_laws p (q.seq .skip) n B s).2.1 hp
    ((ram_safe_laws q .skip n B (p.eval s)).2.1 hq ⟨hq.2, hq.2⟩)

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n ≤ N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) : RAMSafe validateCell B s := by
  let r := read i j bitA (by decide)
  let x := r.eval s
  let r' := read j i bitB (by decide)
  let y := r'.eval x
  have hr : RAMSafe r B s := read_safe i j bitA (by decide) B N s hs hi hn hj hB hpos
  have hr' : RAMSafe r' B x := read_safe j i bitB (by decide) B N x hr.2
    (by simpa [x, r, read_eval, RAMState.set] using hj)
    (by simpa [x, r, read_eval, RAMState.set] using hn)
    (by simpa [x, r, read_eval, RAMState.set] using hi) hB hpos
  have hz : RAMSafe (.zero good : Code) B y :=
    ⟨hr'.2, ram_bound_set B y hr'.2 good 0 (Nat.zero_le _)⟩
  have hinner := (ram_safe_laws .skip (.zero good) bitB B y).2.2 ⟨hr'.2, hr'.2⟩ hz
  have htrue := two r' (.branch bitB .skip (.zero good)) B x hr' hinner
  exact two r _ B s hr
    ((ram_safe_laws _ .skip bitA B x).2.2 htrue ⟨hr.2, hr.2⟩)

#print axioms solution
