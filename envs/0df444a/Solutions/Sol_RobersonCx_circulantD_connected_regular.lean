-- Prove2me | solution 1 for RobersonCx.circulantD_connected_regular
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-27T01:31:11.745853+00:00
-- url     : https://prove2.me/submissions/d0e573eb-2d26-4b64-9337-4b541150a9f1

import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

open RobersonCx

private theorem offsetDistinct {n a b : ℕ} (v : ZMod n) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : v + (a : ZMod n) ≠ v + (b : ZMod n) := by
  intro he
  apply hab
  have he' := congrArg ZMod.val (add_left_cancel he)
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using he'

private theorem adjOffsets {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (x y : ZMod n) :
    (circulantD n r).Adj x y ↔
      y = x + 1 ∨ y = x + (r : ZMod n) ∨
      y = x + ((n - r : ℕ) : ZMod n) ∨ y = x + ((n - 1 : ℕ) : ZMod n) := by
  have minusR : ((n - r : ℕ) : ZMod n) = -(r : ZMod n) := by
    rw [Nat.cast_sub (by omega : r ≤ n), ZMod.natCast_self, zero_sub]
  have minusOne : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have stepNe (a : ℕ) (ha : 0 < a) (ha' : a < n) : x ≠ x + (a : ZMod n) := by
    simpa only [Nat.cast_zero, add_zero] using
      offsetDistinct (a := 0) x (by omega) ha' (by omega)
  simp only [circulantD, SimpleGraph.circulantGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, (h | h) | (h | h)⟩
    · exact .inr (.inr (.inr (by rw [minusOne]; linear_combination -h)))
    · exact .inr (.inr (.inl (by rw [minusR]; linear_combination -h)))
    · exact .inl (by linear_combination h)
    · exact .inr (.inl (by linear_combination h))
  · rintro (h | h | h | h)
    · refine ⟨?_, .inr (.inl (by linear_combination h))⟩
      rw [h, ← Nat.cast_one (R := ZMod n)]
      exact stepNe 1 (by omega) (by omega)
    · refine ⟨?_, .inr (.inr (by linear_combination h))⟩
      rw [h]
      exact stepNe r (by omega) (by omega)
    · have he : x - y = (r : ZMod n) := by
        rw [minusR] at h
        linear_combination -h
      refine ⟨?_, .inl (.inr he)⟩
      rw [h]
      exact stepNe (n - r) (by omega) (by omega)
    · have he : x - y = 1 := by
        rw [minusOne] at h
        linear_combination -h
      refine ⟨?_, .inl (.inl he)⟩
      rw [h]
      exact stepNe (n - 1) (by omega) (by omega)

private theorem fourNeighbors {r n : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (v : ZMod n) : ((circulantD n r).neighborSet v).ncard = 4 := by
  let a := v + 1
  let b := v + (r : ZMod n)
  let c := v + ((n - r : ℕ) : ZMod n)
  let d := v + ((n - 1 : ℕ) : ZMod n)
  have hs : (circulantD n r).neighborSet v = ({a,b,c,d} : Set (ZMod n)) := by
    ext x
    simpa only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff, a, b, c, d] using
      (adjOffsets hr hn v x)
  have hpair {i j : ℕ} (hi : i < j) (hj : j < n) :
      v + (i : ZMod n) ≠ v + (j : ZMod n) :=
    offsetDistinct v (hi.trans hj) hj hi.ne
  have ab : a ≠ b := by simpa only [a,b,Nat.cast_one] using hpair (i:=1) (j:=r) (by omega) (by omega)
  have ac : a ≠ c := by simpa only [a,c,Nat.cast_one] using hpair (i:=1) (j:=n-r) (by omega) (by omega)
  have ad : a ≠ d := by simpa only [a,d,Nat.cast_one] using hpair (i:=1) (j:=n-1) (by omega) (by omega)
  have bc : b ≠ c := hpair (by omega : r < n-r) (by omega)
  have bd : b ≠ d := hpair (by omega : r < n-1) (by omega)
  have cd : c ≠ d := hpair (by omega : n-r < n-1) (by omega)
  have ha : a ∉ ({b,c,d} : Set (ZMod n)) := by simp [ab,ac,ad]
  have hb : b ∉ ({c,d} : Set (ZMod n)) := by simp [bc,bd]
  have hc : c ∉ ({d} : Set (ZMod n)) := by simpa using cd
  rw [hs, Set.ncard_insert_of_notMem ha, Set.ncard_insert_of_notMem hb,
    Set.ncard_insert_of_notMem hc, Set.ncard_singleton]

private theorem shortConnected {r n : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n) :
    (circulantD n r).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨0, ?_⟩
  have reach (j : ℕ) : (circulantD n r).Reachable (0 : ZMod n) (j : ZMod n) := by
    induction j with
    | zero =>
      simpa only [Nat.cast_zero] using
        (SimpleGraph.Reachable.rfl : (circulantD n r).Reachable (0 : ZMod n) 0)
    | succ j ih =>
      rw [Nat.cast_succ]
      exact ih.trans (((adjOffsets hr hn _ _).2 (.inl rfl)).reachable)
  intro x
  simpa only [ZMod.natCast_zmod_val] using reach x.val

theorem solution (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    (circulantD n r).Connected ∧ ∀ v : ZMod n, ((circulantD n r).neighborSet v).ncard = 4 := by
  have : NeZero n := ⟨by omega⟩
  exact ⟨shortConnected hr hn, fourNeighbors hr hn⟩
