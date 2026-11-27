-- Prove2me | solution 1 for RobersonCx.splitB_cubic_bipartite_connected
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-27T00:44:24.636003+00:00
-- url     : https://prove2.me/submissions/7ba026d3-2903-4bd7-8fa0-5097bb848443

import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_IsCyclicInterval

set_option autoImplicit false

open RobersonCx

private theorem adjRightLeft {n r : ℕ} (j i : ZMod n) :
    (splitB n r).Adj (Sum.inr j) (Sum.inl i) ↔ i = j ∨ i = j + 1 ∨ i = j + (r : ZMod n) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem adjLeftRight {n r : ℕ} (i j : ZMod n) :
    (splitB n r).Adj (Sum.inl i) (Sum.inr j) ↔ j = i ∨ j = i - 1 ∨ j = i - (r : ZMod n) := by
  constructor
  · intro h
    rcases (adjRightLeft j i).1 h.symm with h | h | h
    · exact .inl h.symm
    · exact .inr (.inl (by linear_combination -h))
    · exact .inr (.inr (by linear_combination -h))
  · intro h
    apply SimpleGraph.Adj.symm
    apply (adjRightLeft j i).2
    rcases h with h | h | h
    · exact .inl h.symm
    · exact .inr (.inl (by linear_combination -h))
    · exact .inr (.inr (by linear_combination -h))

private theorem adjNotLeftLeft {n r : ℕ} (i j : ZMod n) :
    ¬ (splitB n r).Adj (Sum.inl i) (Sum.inl j) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem adjNotRightRight {n r : ℕ} (i j : ZMod n) :
    ¬ (splitB n r).Adj (Sum.inr i) (Sum.inr j) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem castDistinct {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  intro he
  apply hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val he

private theorem threeElements {V : Type} (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set V).ncard = 3 := by
  have ha : a ∉ ({b, c} : Set V) := by simp [hab, hac]
  have hb : b ∉ ({c} : Set V) := by simpa using hbc
  rw [Set.ncard_insert_of_notMem ha, Set.ncard_insert_of_notMem hb, Set.ncard_singleton]

-- The neighbor triples translate by the same amount at every vertex of a fixed tag.
private theorem splitDegree {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (v : ZMod n ⊕ ZMod n) :
    ((splitB n r).neighborSet v).ncard = 3 := by
  have h01 : (0 : ZMod n) ≠ 1 := by
    simpa using castDistinct (a := 0) (b := 1) (by omega : 0 < n) (by omega) (by omega)
  have h0r : (0 : ZMod n) ≠ (r : ZMod n) := by
    simpa using castDistinct (a := 0) (b := r) (by omega : 0 < n) (by omega) (by omega)
  have h1r : (1 : ZMod n) ≠ (r : ZMod n) := by
    simpa using castDistinct (a := 1) (b := r) (by omega : 1 < n) (by omega) (by omega)
  cases v with
  | inl i =>
    have hs : (splitB n r).neighborSet (Sum.inl i) =
        ({Sum.inr i, Sum.inr (i - 1), Sum.inr (i - (r : ZMod n))} : Set (ZMod n ⊕ ZMod n)) := by
      ext j
      cases j with
      | inl j => simp [SimpleGraph.mem_neighborSet, adjNotLeftLeft]
      | inr j => simp [SimpleGraph.mem_neighborSet, adjLeftRight]
    rw [hs]
    apply threeElements
    · intro h
      exact h01 (by linear_combination -(Sum.inr.inj h))
    · intro h
      exact h0r (by linear_combination -(Sum.inr.inj h))
    · intro h
      exact h1r (by linear_combination -(Sum.inr.inj h))
  | inr i =>
    have hs : (splitB n r).neighborSet (Sum.inr i) =
        ({Sum.inl i, Sum.inl (i + 1), Sum.inl (i + (r : ZMod n))} : Set (ZMod n ⊕ ZMod n)) := by
      ext j
      cases j with
      | inl j => simp [SimpleGraph.mem_neighborSet, adjRightLeft]
      | inr j => simp [SimpleGraph.mem_neighborSet, adjNotRightRight]
    rw [hs]
    apply threeElements
    · intro h
      exact h01 (by linear_combination Sum.inl.inj h)
    · intro h
      exact h0r (by linear_combination Sum.inl.inj h)
    · intro h
      exact h1r (by linear_combination Sum.inl.inj h)

private theorem splitColorable (n r : ℕ) : (splitB n r).Colorable 2 := by
  let color : ZMod n ⊕ ZMod n → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro x y h
  cases x <;> cases y
  · exact (adjNotLeftLeft _ _ h).elim
  · change (0 : Fin 2) ≠ 1
    decide
  · change (1 : Fin 2) ≠ 0
    decide
  · exact (adjNotRightRight _ _ h).elim

-- Position 2i is the left vertex at index i and position 2i+1 is the right vertex.
private def indexCode {n : ℕ} : ZMod n ⊕ ZMod n → ZMod (2 * n)
  | Sum.inl i => ((2 * i.val : ℕ) : ZMod (2 * n))
  | Sum.inr i => ((2 * i.val + 1 : ℕ) : ZMod (2 * n))

private theorem indexCodeVal {n : ℕ} [NeZero n] (i : ZMod n) :
    (indexCode (Sum.inl i)).val = 2 * i.val ∧ (indexCode (Sum.inr i)).val = 2 * i.val + 1 := by
  have hi := ZMod.val_lt i
  exact ⟨ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)⟩

private noncomputable def indexEquiv (n : ℕ) [NeZero n] :
    (ZMod n ⊕ ZMod n) ≃ ZMod (2 * n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have : NeZero (2 * n) := ⟨by omega⟩
  apply Equiv.ofBijective indexCode
  constructor
  · intro x y h
    have he := congrArg ZMod.val h
    cases x <;> cases y
    · rename_i a b
      rw [(indexCodeVal a).1, (indexCodeVal b).1] at he
      exact congrArg Sum.inl (ZMod.val_injective n (by omega))
    · rename_i a b
      rw [(indexCodeVal a).1, (indexCodeVal b).2] at he
      omega
    · rename_i a b
      rw [(indexCodeVal a).2, (indexCodeVal b).1] at he
      omega
    · rename_i a b
      rw [(indexCodeVal a).2, (indexCodeVal b).2] at he
      exact congrArg Sum.inr (ZMod.val_injective n (by omega))
  · intro z
    have hz := ZMod.val_lt z
    let a : ZMod n := ((z.val / 2 : ℕ) : ZMod n)
    have ha : a.val = z.val / 2 := ZMod.val_natCast_of_lt (by omega)
    by_cases h : z.val % 2 = 0
    · exact ⟨Sum.inl a, ZMod.val_injective _ (by rw [(indexCodeVal a).1, ha]; omega)⟩
    · exact ⟨Sum.inr a, ZMod.val_injective _ (by rw [(indexCodeVal a).2, ha]; omega)⟩

private def shortNext {n : ℕ} : ZMod n ⊕ ZMod n → ZMod n ⊕ ZMod n
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl (i + 1)

private theorem indexCodeNext {n : ℕ} [NeZero n] (v : ZMod n ⊕ ZMod n) :
    indexCode (shortNext v) = indexCode v + 1 := by
  cases v with
  | inl i =>
    change ((2 * i.val + 1 : ℕ) : ZMod (2 * n)) = ((2 * i.val : ℕ) : ZMod (2 * n)) + 1
    rw [Nat.cast_add, Nat.cast_one]
  | inr i =>
    have hi := ZMod.val_lt i
    have hc : ((i.val + 1 : ℕ) : ZMod n) = i + 1 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
    change ((2 * (i + 1).val : ℕ) : ZMod (2 * n)) =
      ((2 * i.val + 1 : ℕ) : ZMod (2 * n)) + 1
    rw [← hc]
    by_cases ht : i.val + 1 < n
    · have hcoord : (((i.val + 1 : ℕ) : ZMod n)).val = i.val + 1 :=
        ZMod.val_natCast_of_lt ht
      rw [hcoord, ← Nat.cast_one (R := ZMod (2 * n)), ← Nat.cast_add]
      congr 1
    · have hlast : i.val + 1 = n := by omega
      have hz : (((i.val + 1 : ℕ) : ZMod n)).val = 0 := by
        rw [hlast, ZMod.natCast_self, ZMod.val_zero]
      rw [hz, Nat.mul_zero, Nat.cast_zero, ← Nat.cast_one (R := ZMod (2 * n)), ← Nat.cast_add]
      rw [show 2 * i.val + 1 + 1 = 2 * n by omega, ZMod.natCast_self]

private theorem shortNextAdj {n r : ℕ} (v : ZMod n ⊕ ZMod n) :
    (splitB n r).Adj v (shortNext v) := by
  cases v with
  | inl i => exact ((adjRightLeft i i).2 (.inl rfl)).symm
  | inr i => exact (adjRightLeft i (i + 1)).2 (.inr (.inl rfl))

private theorem swapEdge {V : Type} (x y : V) : s(x, y) = s(y, x) :=
  Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)

private theorem shortHamilton {n r : ℕ} [NeZero n] (hn : 3 ≤ 2 * n) :
    ∃ c : ZMod (2 * n) ≃ (ZMod n ⊕ ZMod n), IsHamCycle (splitB n r) c ∧
      cycleEdges c = {e | ∃ i : ZMod n, e = s(Sum.inr i, Sum.inl i) ∨ e = s(Sum.inr i, Sum.inl (i + 1))} := by
  let p := indexEquiv n
  let c := p.symm
  have next (i : ZMod (2 * n)) : c (i + 1) = shortNext (c i) := by
    apply p.injective
    calc
      p (c (i + 1)) = i + 1 := p.apply_symm_apply _
      _ = p (c i) + 1 := by rw [p.apply_symm_apply]
      _ = p (shortNext (c i)) := (indexCodeNext (c i)).symm
  refine ⟨c, ⟨hn, fun i => ?_⟩, ?_⟩
  · rw [next]
    exact shortNextAdj _
  · ext e
    constructor
    · rintro ⟨i, rfl⟩
      rw [next]
      change ∃ j : ZMod n, s(c i, shortNext (c i)) = s(Sum.inr j, Sum.inl j) ∨
        s(c i, shortNext (c i)) = s(Sum.inr j, Sum.inl (j + 1))
      cases hc : c i with
      | inl j => exact ⟨j, .inl (swapEdge _ _)⟩
      | inr j => exact ⟨j, .inr rfl⟩
    · rintro ⟨j, he | he⟩
      · refine ⟨p (Sum.inl j), ?_⟩
        have hj : c (p (Sum.inl j)) = Sum.inl j := p.symm_apply_apply _
        rw [next, hj]
        exact he.trans (swapEdge _ _)
      · refine ⟨p (Sum.inr j), ?_⟩
        have hj : c (p (Sum.inr j)) = Sum.inr j := p.symm_apply_apply _
        rw [next, hj]
        exact he

private theorem connectedAlongCycle {V : Type} {N : ℕ} [NeZero N] {G : SimpleGraph V}
    (c : ZMod N ≃ V) (hc : IsHamCycle G c) : G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).2
  refine ⟨c 0, ?_⟩
  have reach (k : ℕ) : G.Reachable (c 0) (c (k : ZMod N)) := by
    induction k with
    | zero =>
      simpa only [Nat.cast_zero] using (SimpleGraph.Reachable.rfl : G.Reachable (c 0) (c 0))
    | succ k ih =>
      rw [Nat.cast_succ]
      exact ih.trans ((hc.2 (k : ZMod N)).reachable)
  intro v
  simpa only [ZMod.natCast_zmod_val, Equiv.apply_symm_apply] using reach (c.symm v).val

theorem solution (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    (∀ v : ZMod n ⊕ ZMod n, ((splitB n r).neighborSet v).ncard = 3) ∧ (splitB n r).Colorable 2 ∧
    (∃ c : ZMod (2 * n) ≃ (ZMod n ⊕ ZMod n), IsHamCycle (splitB n r) c ∧
      cycleEdges c = {e | ∃ i : ZMod n, e = s(Sum.inr i, Sum.inl i) ∨ e = s(Sum.inr i, Sum.inl (i + 1))}) ∧
    (splitB n r).Connected := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨c, hc, he⟩ := shortHamilton (r := r) (n := n) (by omega)
  exact ⟨splitDegree hr hn, splitColorable n r, ⟨c, hc, he⟩, connectedAlongCycle c hc⟩
