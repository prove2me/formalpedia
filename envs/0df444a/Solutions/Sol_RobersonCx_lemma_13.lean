-- Prove2me | solution 1 for RobersonCx.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-27T01:37:16.814944+00:00
-- url     : https://prove2.me/submissions/d4789dac-c1f8-481f-b921-65e1ff63dee1

import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx.ExclusionLocal

open scoped Classical

private theorem pathwidth_linear {V : Type} [Finite V] (G : SimpleGraph V)
    (f : V → ℕ) (hf : Function.Injective f) (s r : ℕ) (hs : 0 < s)
    (fits : ∀ v, f v < s)
    (adjCoords : ∀ u v, G.Adj u v → f u ≤ f v + r ∧ f v ≤ f u + r) :
    PwLE G r := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let W : Fin s → Finset V := fun i =>
    Finset.univ.filter fun x => f x ≤ i.val ∧ i.val ≤ f x + r
  have mem (v : V) (i : Fin s) : v ∈ W i ↔ f v ≤ i.val ∧ i.val ≤ f v + r := by
    simp [W]
  refine ⟨s, W, ⟨hs, ?_, ?_, ?_⟩, ?_⟩
  · intro u v huv
    have ⟨h₁, h₂⟩ := adjCoords u v huv
    let i : Fin s := ⟨max (f u) (f v), max_lt (fits u) (fits v)⟩
    refine ⟨i, (mem u i).2 ⟨le_max_left _ _, ?_⟩, (mem v i).2 ⟨le_max_right _ _, ?_⟩⟩
    · exact max_le (by omega) h₂
    · exact max_le h₁ (by omega)
  · intro v
    exact ⟨⟨f v, fits v⟩, (mem _ _).2 ⟨le_rfl, by change f v ≤ f v + r; omega⟩⟩
  · intro v i j k hij hjk hi hk
    exact (mem _ _).2 ⟨((mem _ _).1 hi).1.trans (show i.val ≤ j.val from hij),
      (show j.val ≤ k.val from hjk).trans ((mem _ _).1 hk).2⟩
  · intro i
    suffices (W i).card ≤ (Finset.Icc (i.val - r) i.val).card by
      rw [Nat.card_Icc] at this
      omega
    apply Finset.card_le_card_of_injOn f _ hf.injOn
    intro v hv
    have ⟨h₁, h₂⟩ := (mem v i).1 (by simpa using hv)
    exact Finset.mem_Icc.2 ⟨by omega, h₁⟩

private theorem pathwidth_add_vertices {V : Type} [Finite V] (G : SimpleGraph V)
    (U : Set V) (k t : ℕ) (hU : U.ncard ≤ t) (h : PwLE (G.induce Uᶜ) k) :
    PwLE G (k + t) := by
  classical
  obtain ⟨s, W, ⟨hs, edges, vertices, intervals⟩, bound⟩ := h
  let emb : (Uᶜ : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let newW : Fin s → Finset V := fun i => U.toFinite.toFinset ∪ (W i).map emb
  have put (i : Fin s) (v : V) (hv : v ∉ U) (hi : (⟨v, hv⟩ : (Uᶜ : Set V)) ∈ W i) :
      v ∈ newW i :=
    Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨v, hv⟩, hi, rfl⟩)
  have putU (i : Fin s) (v : V) (hv : v ∈ U) : v ∈ newW i :=
    Finset.mem_union_left _ (by simpa using hv)
  have get (i : Fin s) (v : V) (hv : v ∉ U) (hi : v ∈ newW i) :
      (⟨v, hv⟩ : (Uᶜ : Set V)) ∈ W i := by
    rcases Finset.mem_union.1 hi with hm | hm
    · exact (hv (by simpa using hm)).elim
    · obtain ⟨w, hw, heq⟩ := Finset.mem_map.1 hm
      have : w = ⟨v, hv⟩ := Subtype.ext heq
      rwa [← this]
  refine ⟨s, newW, ⟨hs, ?_, ?_, ?_⟩, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U
    · exact ⟨⟨0, hs⟩, putU _ _ hu, putU _ _ hv⟩
    · obtain ⟨i, hi⟩ := vertices ⟨v, hv⟩
      exact ⟨i, putU _ _ hu, put _ _ hv hi⟩
    · obtain ⟨i, hi⟩ := vertices ⟨u, hu⟩
      exact ⟨i, put _ _ hu hi, putU _ _ hv⟩
    · obtain ⟨i, hi, hj⟩ := edges ⟨u, hu⟩ ⟨v, hv⟩ huv
      exact ⟨i, put _ _ hu hi, put _ _ hv hj⟩
  · intro v
    by_cases hv : v ∈ U
    · exact ⟨⟨0, hs⟩, putU _ _ hv⟩
    · obtain ⟨i, hi⟩ := vertices ⟨v, hv⟩
      exact ⟨i, put _ _ hv hi⟩
  · intro v i j l hij hjl hi hl
    by_cases hv : v ∈ U
    · exact putU _ _ hv
    · exact put _ _ hv (intervals ⟨v, hv⟩ _ _ _ hij hjl (get _ _ hv hi) (get _ _ hv hl))
  · intro i
    have hc := Finset.card_union_le U.toFinite.toFinset ((W i).map emb)
    rw [Finset.card_map, ← Set.ncard_eq_toFinset_card] at hc
    have hi := bound i
    change (U.toFinite.toFinset ∪ (W i).map emb).card ≤ k + t + 1
    omega

private def coordinate {n : ℕ} (a x : ZMod n) : ℕ := (x - a).val

private theorem coordinate_spec {n : ℕ} [NeZero n] (a x : ZMod n) :
    a + (coordinate a x : ZMod n) = x := by
  simp [coordinate]

private theorem coordinate_lt {n : ℕ} [NeZero n] (a x : ZMod n) : coordinate a x < n :=
  ZMod.val_lt _

private theorem coordinate_injective {n : ℕ} [NeZero n] (a : ZMod n) :
    Function.Injective (coordinate a) := by
  intro x y h
  rw [← coordinate_spec a x, ← coordinate_spec a y, h]

private theorem coordinate_step {n : ℕ} [NeZero n] (a x : ZMod n) (k : ℕ) (hk : k < n) :
    coordinate a (x + (k : ZMod n)) = coordinate a x + k ∨
      coordinate a x + k = coordinate a (x + (k : ZMod n)) + n := by
  have key : x + (k : ZMod n) - a = ((coordinate a x + k : ℕ) : ZMod n) := by
    rw [Nat.cast_add, coordinate, ZMod.natCast_zmod_val]
    abel
  have hval : coordinate a (x + (k : ZMod n)) = (coordinate a x + k) % n := by
    simp only [coordinate, key, ZMod.val_natCast]
  have hx := coordinate_lt a x
  by_cases hw : coordinate a x + k < n
  · exact .inl (hval.trans (Nat.mod_eq_of_lt hw))
  · rw [hval, Nat.mod_eq_sub_mod (by omega : n ≤ coordinate a x + k),
      Nat.mod_eq_of_lt (by omega : coordinate a x + k - n < n)]
    exact .inr (by omega)

private theorem circulant_adj_oriented {n r : ℕ} {x y : ZMod n} (h : (circulantD n r).Adj x y) :
    ∃ k : ℕ, (k = 1 ∨ k = r) ∧ (y = x + (k : ZMod n) ∨ x = y + (k : ZMod n)) := by
  simp only [circulantD, SimpleGraph.circulantGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h.2 with (h | h) | (h | h)
  · exact ⟨1, .inl rfl, .inr (by simpa only [Nat.cast_one, add_comm] using (sub_eq_iff_eq_add.mp h))⟩
  · exact ⟨r, .inr rfl, .inr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h))⟩
  · exact ⟨1, .inl rfl, .inl (by simpa only [Nat.cast_one, add_comm] using (sub_eq_iff_eq_add.mp h))⟩
  · exact ⟨r, .inr rfl, .inl (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h))⟩

end RobersonCx.ExclusionLocal

open RobersonCx RobersonCx.ExclusionLocal

theorem solution (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    PwLE (circulantD n r) (2 * r) ∧
    (∀ a : ZMod n,
      PwLE ((circulantD n r).induce ({x | ∃ j < r, x = a + (j : ZMod n)} : Set (ZMod n))ᶜ) r) ∧
    (∀ i : ZMod n, PwLE ((circulantD n r).deleteEdges {s(i, i + (r : ZMod n))}) (2 * r - 1)) := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := by omega
  let G := circulantD n r
  let block (a : ZMod n) : Set (ZMod n) := {x | ∃ j < r, x = a + (j : ZMod n)}
  have window (a : ZMod n) : PwLE (G.induce (block a)ᶜ) r := by
    have stays (x : ↑((block a)ᶜ : Set (ZMod n))) : r ≤ coordinate a x.val := by
      by_contra! hh
      exact x.property ⟨_, hh, (coordinate_spec a x.val).symm⟩
    have nowrap (x y : ↑((block a)ᶜ : Set (ZMod n))) (k : ℕ) (hk : k ≤ r)
        (h : y.val = x.val + (k : ZMod n)) :
        coordinate a y.val = coordinate a x.val + k := by
      have hstep := coordinate_step a x.val k (by omega)
      rw [← h] at hstep
      rcases hstep with he | he
      · exact he
      · have := coordinate_lt a x.val
        have := stays y
        omega
    apply pathwidth_linear _ (fun x : ↑((block a)ᶜ : Set (ZMod n)) => coordinate a x.val)
      ((coordinate_injective a).comp Subtype.val_injective) n r hn0
      (fun x => coordinate_lt a x.val)
    intro x y hxy
    obtain ⟨k, hk, h | h⟩ := circulant_adj_oriented (SimpleGraph.induce_adj.mp hxy)
    all_goals
      have hkr : k ≤ r := by rcases hk with rfl | rfl <;> omega
    · have := nowrap x y k hkr h
      omega
    · have := nowrap y x k hkr h
      omega
  refine ⟨?_, window, ?_⟩
  · have cardBlock : (block 0).ncard ≤ r := by
      rw [Set.ncard_eq_toFinset_card]
      rw [← Finset.card_range r]
      apply Finset.card_le_card_of_injOn (coordinate 0) _ (coordinate_injective 0).injOn
      intro v hv
      have huv : v ∈ block 0 := by simpa [block] using hv
      obtain ⟨j, hj, rfl⟩ := huv
      simpa [coordinate, ZMod.val_natCast_of_lt (by omega : j < n)] using hj
    simpa [two_mul] using pathwidth_add_vertices G (block 0) r r cardBlock (window 0)
  · intro i
    let a : ZMod n := i + (r : ZMod n)
    let U : Set (ZMod n) := {x | n - r < coordinate a x}
    let D := G.deleteEdges {s(i, a)}
    have cardU : U.ncard ≤ r - 1 := by
      rw [Set.ncard_eq_toFinset_card]
      suffices U.toFinite.toFinset.card ≤ (Finset.Icc (n - r + 1) (n - 1)).card by
        rw [Nat.card_Icc] at this
        omega
      apply Finset.card_le_card_of_injOn (coordinate a) _ (coordinate_injective a).injOn
      intro v hv
      have huv : n - r < coordinate a v := show v ∈ U from by simpa [U] using hv
      have hlt := coordinate_lt a v
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have nowrap (x y : ↑(Uᶜ : Set (ZMod n))) (k : ℕ) (hk : k ≤ r)
        (h : y.val = x.val + (k : ZMod n)) (hxy : D.Adj x.val y.val) :
        coordinate a y.val = coordinate a x.val + k := by
      have hstep := coordinate_step a x.val k (by omega)
      rw [← h] at hstep
      rcases hstep with he | he
      · exact he
      · have hxu : ¬ n - r < coordinate a x.val := x.property
        have hx : coordinate a x.val = n - r := by omega
        have hy : coordinate a y.val = 0 := by omega
        have hya : y.val = a := by
          rw [← coordinate_spec a y.val, hy, Nat.cast_zero, add_zero]
        have hxi : x.val = i := by
          rw [← coordinate_spec a x.val, hx, Nat.cast_sub (by omega : r ≤ n), ZMod.natCast_self]
          dsimp [a]
          abel
        exfalso
        exact (SimpleGraph.deleteEdges_adj.mp hxy).2 (by rw [hxi, hya]; exact Set.mem_singleton _)
    have window' : PwLE (D.induce Uᶜ) r := by
      apply pathwidth_linear _ (fun x : ↑(Uᶜ : Set (ZMod n)) => coordinate a x.val)
        ((coordinate_injective a).comp Subtype.val_injective) n r hn0
        (fun x => coordinate_lt a x.val)
      intro x y hxy
      have hxy' : D.Adj x.val y.val := SimpleGraph.induce_adj.mp hxy
      obtain ⟨k, hk, h | h⟩ := circulant_adj_oriented (SimpleGraph.deleteEdges_adj.mp hxy').1
      all_goals
        have hkr : k ≤ r := by rcases hk with rfl | rfl <;> omega
      · have := nowrap x y k hkr h hxy'
        omega
      · have := nowrap y x k hkr h hxy'.symm
        omega
    convert pathwidth_add_vertices D U r (r - 1) cardU window' using 1 <;> omega
