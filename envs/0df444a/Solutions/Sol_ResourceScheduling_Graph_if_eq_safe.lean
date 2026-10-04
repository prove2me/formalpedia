-- Prove2me | solution 1 for ResourceScheduling.Graph.if_eq_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:00:10.499515+00:00
-- url     : https://prove2.me/submissions/bbe908c7-9330-49ef-a4b1-ffdd948a95ba

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

private theorem two (p q : Code) (B : ℕ) (s : RAMState GraphReg)
    (hp : RAMSafe p B s) (hq : RAMSafe q B (p.eval s)) : RAMSafe (block [p,q]) B s := by
  exact (ram_safe_laws p (q.seq .skip) n B s).2.1 hp
    ((ram_safe_laws q .skip n B (p.eval s)).2.1 hq ⟨hq.2, hq.2⟩)

theorem solution (a b : GraphReg) (p q : Code) (B : ℕ) (P : RAMState GraphReg → Prop)
    (hd : ∀ s x, P s → P (s.set delta x)) (ha : ∀ s x, P s → P (s.set aux x))
    (hp : ∀ s, RAMBound B s → P s → RAMSafe p B s)
    (hq : ∀ s, RAMBound B s → P s → RAMSafe q B s)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hP : P s) : RAMSafe (ifEq a b p q) B s := by
  let x := s.set delta (s.val a - s.val b)
  let y := x.set aux (x.val b - x.val a)
  have hx : RAMBound B x := ram_bound_set B s hs delta _ ((Nat.sub_le _ _).trans (hs.1 a))
  have hy : RAMBound B y := ram_bound_set B x hx aux _ ((Nat.sub_le _ _).trans (hx.1 b))
  have hPx : P x := hd s _ hP
  have hPy : P y := ha x _ hPx
  have hinner : RAMSafe (.branch aux q p) B y :=
    (ram_safe_laws q p aux B y).2.2 (hq y hy hPy) (hp y hy hPy)
  have hfalse : RAMSafe (block [.sub b a aux, .branch aux q p]) B x :=
    two _ _ B x ⟨hx, hy⟩ hinner
  exact two _ _ B s ⟨hs, hx⟩
    ((ram_safe_laws q _ delta B x).2.2 (hq x hx hPx) hfalse)

#print axioms solution
