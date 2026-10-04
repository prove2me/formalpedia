-- Prove2me | solution 1 for ResourceScheduling.Graph.non_edge_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:00:13.874682+00:00
-- url     : https://prove2.me/submissions/a393121b-8295-49eb-8a60-e4513cf4e62f

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

theorem solution (p : Code) (B N : ℕ) (P : RAMState GraphReg → Prop)
    (hP : ∀ v ∈ [delta, index, bitA], ∀ s x, P s → P (s.set v x))
    (hp : ∀ s, RAMBound B s → P s → RAMSafe p B s)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hPs : P s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n ≤ N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) : RAMSafe (ifNonEdge p) B s := by
  let x := s.set delta (s.val j - s.val i)
  let r := read i j bitA (by decide)
  let y := r.eval x
  have hx : RAMBound B x := ram_bound_set B s hs delta _ ((Nat.sub_le _ _).trans (hs.1 j))
  have hPx : P x := hP delta (by simp) s _ hPs
  have hr : RAMSafe r B x := read_safe i j bitA (by decide) B N x hx
    (by simpa [x, RAMState.set] using hi) (by simpa [x, RAMState.set] using hn)
    (by simpa [x, RAMState.set] using hj) hB hpos
  have hPy : P y := by
    rw [show y = (x.set index (x.val i * x.val n + x.val j)).set bitA
      (if x.word.getD (x.val i * x.val n + x.val j) Letter.sep = Letter.one then 1 else 0)
      from read_eval i j bitA (by decide) x]
    exact hP bitA (by simp) _ _ (hP index (by simp) _ _ hPx)
  have hinner := (ram_safe_laws .skip p bitA B y).2.2 ⟨hr.2, hr.2⟩ (hp y hr.2 hPy)
  have htrue := two r (.branch bitA .skip p) B x hr hinner
  exact two _ _ B s ⟨hs, hx⟩
    ((ram_safe_laws _ .skip delta B x).2.2 htrue ⟨hx, hx⟩)

#print axioms solution
