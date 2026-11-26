-- Prove2me | solution 1 for RobersonCx.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-26T20:25:35.298797+00:00
-- url     : https://prove2.me/submissions/f1260fb1-b8e7-4f99-9255-ab508ce29982

import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_RobersonCx_IsImmersion
import Definitions.Def_RobersonCx_TwLE
import Definitions.Def_RobersonCx_aInv
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx.ExclusionLocal

-- Restrict a minor model after deleting vertices that its retained branch sets avoid.

private theorem minor_avoid_deleted_vertices {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (B : W → Set V)
    (bcon : ∀ w, (G.induce (B w)).Connected)
    (bdisj : ∀ w w', w ≠ w' → Disjoint (B w) (B w'))
    (bedge : ∀ w w', H.Adj w w' → ∃ x ∈ B w, ∃ y ∈ B w', G.Adj x y)
    (U : Set V) (S : Set W) (avoid : ∀ w ∉ S, Disjoint (B w) U) :
    HadwigerConj.IsMinor (H.induce Sᶜ) (G.induce Uᶜ) := by
  let newBranch : ↑(Sᶜ : Set W) → Set ↑(Uᶜ : Set V) := fun w => {x | x.val ∈ B w.val}
  have outside (w : ↑(Sᶜ : Set W)) {x : V} (hx : x ∈ B w.val) : x ∉ U :=
    (Set.disjoint_left.mp (avoid w.val w.property)) hx
  refine ⟨newBranch, ?_, ?_, ?_⟩
  · intro w
    let e : (G.induce (B w.val)) ≃g ((G.induce Uᶜ).induce (newBranch w)) :=
      { toFun := fun x => ⟨⟨x.val, outside w x.property⟩, x.property⟩
        invFun := fun x => ⟨x.val.val, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact (SimpleGraph.Iso.connected_iff e).mp (bcon w.val)
  · intro w w' hne
    apply Set.disjoint_left.mpr
    intro x hx hx'
    have hne' : w.val ≠ w'.val := fun eq => hne (Subtype.ext eq)
    exact (Set.disjoint_left.mp (bdisj w.val w'.val hne')) hx hx'
  · intro w w' h
    obtain ⟨x, hx, y, hy, hxy⟩ := bedge w.val w'.val h
    exact ⟨⟨x, outside w hx⟩, hx, ⟨y, outside w' hy⟩, hy, hxy⟩

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Build path decompositions from intervals in linearized circulant coordinates.

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

private theorem pathwidth_D_upper (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
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

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Intersect the occurrence intervals of many disjoint connected blocks in a path decomposition.

private def Touches {V : Type} {s : ℕ} (W : Fin s → Finset V) (U : Set V) (i : Fin s) : Prop :=
  ∃ v ∈ U, v ∈ W i

private theorem touches_interval {V : Type} {G : SimpleGraph V} {s : ℕ} {W : Fin s → Finset V}
    (h : GaussianSweep.IsPathDecomposition G s W) {U : Set V} (hU : (G.induce U).Connected)
    {i j k : Fin s} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : Touches W U i) (hk : Touches W U k) : Touches W U j := by
  classical
  by_contra hj
  obtain ⟨u, hu, hui⟩ := hi
  obtain ⟨v, hv, hvk⟩ := hk
  let Left (x : U) := ∃ t : Fin s, t ≤ j ∧ x.val ∈ W t
  have off (x : U) : x.val ∉ W j := fun hmem => hj ⟨x.val, x.property, hmem⟩
  have edge_left {x y : U} (hxy : (G.induce U).Adj x y) (hx : Left x) : Left y := by
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hxb, hyb⟩ := h.2.1 _ _ hxy
    have hb : b ≤ j := by
      by_contra! hab
      exact off x (h.2.2.2 _ _ _ _ ha hab.le hxa hxb)
    exact ⟨b, hb, hyb⟩
  have walk_left {x y : U} (p : (G.induce U).Walk x y) : Left x → Left y := by
    induction p with
    | nil => exact id
    | cons he _ ih => exact fun hx => ih (edge_left he hx)
  obtain ⟨p⟩ := hU.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨a, ha, hva⟩ := walk_left p ⟨i, hij, hui⟩
  exact off ⟨v, hv⟩ (h.2.2.2 _ _ _ _ ha hjk hva hvk)

private theorem last_touch {V : Type} {G : SimpleGraph V} {s : ℕ} {W : Fin s → Finset V}
    (h : GaussianSweep.IsPathDecomposition G s W) {U : Set V} (hU : U.Nonempty) :
    ∃ i, Touches W U i ∧ ∀ j, Touches W U j → j ≤ i := by
  classical
  let indices : Finset (Fin s) := Finset.univ.filter (Touches W U)
  have mem (i : Fin s) : i ∈ indices ↔ Touches W U i := by simp [indices]
  obtain ⟨v, hv⟩ := hU
  obtain ⟨i, hi⟩ := h.2.2.1 v
  have hne : indices.Nonempty := ⟨i, (mem i).2 ⟨v, hv, hi⟩⟩
  exact ⟨indices.max' hne, (mem _).1 (indices.max'_mem hne),
    fun j hj => indices.le_max' j ((mem j).2 hj)⟩

private theorem pathwidth_disjoint_blocks {V I : Type} [Fintype I] (G : SimpleGraph V)
    (A : I → Set V) (k : ℕ) (hk : 0 < k) (hcount : k < Fintype.card I)
    (hconnected : ∀ i, (G.induce (A i)).Connected)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hpaths : ∀ i j, i ≠ j → ∀ S : Finset V, S.card < k →
      Disjoint (A i) (S : Set V) → Disjoint (A j) (S : Set V) →
      ∃ u v : ↑((S : Set V)ᶜ), u.val ∈ A i ∧ v.val ∈ A j ∧
        (G.induce ((S : Set V)ᶜ)).Reachable u v) :
    ¬ PwLE G (k - 1) := by
  classical
  rintro ⟨s, W, decomp, hcard⟩
  have hcard' (t : Fin s) : (W t).card ≤ k := by have := hcard t; omega
  have hnonempty (i : I) : (A i).Nonempty := by
    obtain ⟨v⟩ := (hconnected i).nonempty
    exact ⟨v.val, v.property⟩
  choose last hlast hmax using fun i => last_touch decomp (hnonempty i)
  have pairwiseTouch (a b : I) (hne : a ≠ b) (hab : last a ≤ last b) :
      ∃ t, Touches W (A a) t ∧ Touches W (A b) t := by
    by_contra! h
    let t := last a
    have ht : Touches W (A a) t := hlast a
    have tb : t < last b := by
      by_contra! hb
      have he : last a = last b := le_antisymm hab hb
      exact h (last b) (he ▸ ht) (hlast b)
    let next : Fin s := ⟨t.val + 1, by have := (last b).isLt; exact Nat.lt_of_le_of_lt tb this⟩
    let S : Finset V := W t ∩ W next
    have hnext : t < next := Nat.lt_succ_self _
    have forbids_a (i : Fin s) (hi : t < i) : ¬ Touches W (A a) i :=
      fun htouch => (not_le_of_gt hi) (hmax a i htouch)
    have forbids_b (i : Fin s) (hi : i ≤ t) : ¬ Touches W (A b) i :=
      fun htouch => h t ht (touches_interval decomp (hconnected b) hi hab htouch (hlast b))
    have disj_a : Disjoint (A a) (S : Set V) := by
      refine Set.disjoint_left.2 ?_
      intro v hv hvS
      exact forbids_a next hnext ⟨v, hv, (Finset.mem_inter.1 (show v ∈ S from hvS)).2⟩
    have disj_b : Disjoint (A b) (S : Set V) := by
      refine Set.disjoint_left.2 ?_
      intro v hv hvS
      exact forbids_b t le_rfl ⟨v, hv, (Finset.mem_inter.1 (show v ∈ S from hvS)).1⟩
    obtain ⟨z, hzA, hzW⟩ := ht
    have hzS : z ∉ S := fun hz => Set.disjoint_left.1 disj_a hzA hz
    have hkS : S.card < k := by
      have hsub : insert z S ⊆ W t := by
        intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hzW
        · exact (Finset.mem_inter.1 hv).1
      have hh := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hzS] at hh
      have := hcard' t
      omega
    obtain ⟨u, v, hu, hv, ⟨p⟩⟩ := hpaths a b hne S hkS disj_a disj_b
    let Left (z : ↑((S : Set V)ᶜ)) := ∃ i : Fin s, i ≤ t ∧ z.val ∈ W i
    have stays {x y : ↑((S : Set V)ᶜ)} (he : (G.induce ((S : Set V)ᶜ)).Adj x y)
        (hx : Left x) : Left y := by
      obtain ⟨i, hi, hxi⟩ := hx
      obtain ⟨j, hxj, hyj⟩ := decomp.2.1 _ _ he
      have hj : j ≤ t := by
        by_contra! hj
        have hnj : next ≤ j := hj
        have hxt := decomp.2.2.2 _ _ _ _ hi hj.le hxi hxj
        have hxn := decomp.2.2.2 _ _ _ _ (hi.trans hnext.le) hnj hxi hxj
        exact x.property (Finset.mem_inter.2 ⟨hxt, hxn⟩)
      exact ⟨j, hj, hyj⟩
    have walk_stays {x y : ↑((S : Set V)ᶜ)} (q : (G.induce ((S : Set V)ᶜ)).Walk x y) :
        Left x → Left y := by
      induction q with
      | nil => exact id
      | cons he _ ih => exact fun hx => ih (stays he hx)
    obtain ⟨i, hi⟩ := decomp.2.2.1 u.val
    obtain ⟨j, hj, hvj⟩ := walk_stays p ⟨i, hmax a i ⟨u.val, hu, hi⟩, hi⟩
    exact forbids_b j hj ⟨v.val, hv, hvj⟩
  have imageNonempty : (Finset.univ.image last).Nonempty := by
    have hi : 0 < Fintype.card I := by omega
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp hi
    exact ⟨last a, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩
  let t := (Finset.univ.image last).min' imageNonempty
  obtain ⟨a, -, hat⟩ := Finset.mem_image.1 ((Finset.univ.image last).min'_mem imageNonempty)
  have allTouch (b : I) : Touches W (A b) (last a) := by
    by_cases hab : a = b
    · rw [← hab]
      exact hlast a
    · have ht : last a ≤ last b := by
        rw [hat]
        exact (Finset.univ.image last).min'_le _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
      obtain ⟨j, hja, hjb⟩ := pairwiseTouch a b hab ht
      exact touches_interval decomp (hconnected b) (hmax a j hja) ht hjb (hlast b)
  choose f hfA hfW using allTouch
  have hinj : Function.Injective f := by
    intro a b he
    by_contra! hab
    exact Set.disjoint_left.1 (hdisjoint a b hab) (hfA a) (he.symm ▸ hfA b)
  have hl : Fintype.card I ≤ (W (last a)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card_of_injOn f (fun a _ => hfW a) hinj.injOn
  exact (not_le_of_gt hcount) (hl.trans (hcard' _))

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Route between two clean blocks via the unused residue on one of the two arcs.

private theorem add_index {n : ℕ} [NeZero n] (o : ZMod n) (j : ℕ) (hj : j < n) :
    coordinate o (o + (j : ZMod n)) = j := by
  rw [coordinate, add_sub_cancel_left, ZMod.val_natCast_of_lt hj]

private theorem d_step {n r k : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n)
    (x : ZMod n) (hk : k = 1 ∨ k = r) :
    (circulantD n r).Adj x (x + (k : ZMod n)) := by
  have hpos : 0 < k := by rcases hk with rfl | rfl <;> omega
  have hlt : k < n := by rcases hk with rfl | rfl <;> omega
  have nz : (k : ZMod n) ≠ 0 := by
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at h'
    omega
  rw [circulantD, SimpleGraph.circulantGraph_adj]
  refine ⟨?_, .inr ?_⟩
  · intro h
    apply nz
    exact add_left_cancel (show x + (k : ZMod n) = x + 0 by simpa using h.symm)
  · rw [add_sub_cancel_left]
    rcases hk with rfl | rfl <;> simp

private def cutD (n r : ℕ) (o : ZMod n) : SimpleGraph (ZMod n) :=
  (circulantD n r).deleteEdges {s(o - 1, o)}

private theorem long_survives {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n)
    (o x : ZMod n) : (cutD n r o).Adj x (x + (r : ZMod n)) := by
  rw [cutD, SimpleGraph.deleteEdges_adj]
  refine ⟨d_step hr hn x (.inr rfl), ?_⟩
  intro he
  rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 he) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have heq : (r : ZMod n) = (1 : ℕ) := by linear_combination h₂ - h₁
    have e := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by omega : r < n),
      ZMod.val_natCast_of_lt (by omega : 1 < n)] at e
    omega
  · have heq : ((r + 1 : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_add, Nat.cast_one]
      linear_combination h₂ - h₁
    have e := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by omega : r + 1 < n), ZMod.val_zero] at e
    omega

private theorem short_survives {n r j : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (o : ZMod n) (hj : j + 1 < n) :
    (cutD n r o).Adj (o + (j : ZMod n)) (o + ((j + 1 : ℕ) : ZMod n)) := by
  rw [cutD, SimpleGraph.deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_add, add_assoc] using d_step hr hn (o + (j : ZMod n)) (k := 1) (.inl rfl)
  · have tail_coord : coordinate o (o - 1) = n - 1 := by
      rw [← add_index o (n - 1) (by omega)]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]
      abel
    intro he
    rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 he) with ⟨h₁, _⟩ | ⟨h₁, h₂⟩
    · have h := congrArg (coordinate o) h₁
      rw [add_index o j (by omega), tail_coord] at h
      omega
    · have hy := congrArg (coordinate o) h₂
      rw [add_index o (j + 1) hj, tail_coord] at hy
      have hx := congrArg (coordinate o) h₁
      rw [add_index o j (by omega)] at hx
      have hzero : coordinate o o = 0 := by simp [coordinate]
      rw [hzero] at hx
      omega

private def blockAt {n : ℕ} (o : ZMod n) (a r : ℕ) : Set (ZMod n) :=
  {x | ∃ j : ℕ, a ≤ j ∧ j < a + r ∧ x = o + (j : ZMod n)}

private theorem block_connected {n r a : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (o : ZMod n) (ha : a + r ≤ n) :
    ((cutD n r o).induce (blockAt o a r)).Connected := by
  let A := blockAt o a r
  have mem (t : ℕ) (ht : t < r) : o + ((a + t : ℕ) : ZMod n) ∈ A :=
    ⟨a + t, by omega, by omega, rfl⟩
  let base : A := ⟨o + (a : ZMod n), by simpa using mem 0 (by omega)⟩
  have reach (t : ℕ) (ht : t < r) :
      ((cutD n r o).induce A).Reachable base ⟨o + ((a + t : ℕ) : ZMod n), mem t ht⟩ := by
    induction t with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ t ih =>
      refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
      exact short_survives hr hn o (j := a + t) (by omega)
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨base, ?_⟩
  intro z
  obtain ⟨j, haj, hj, he⟩ := z.property
  have ht : j - a < r := by omega
  have he' : z = ⟨o + ((a + (j - a) : ℕ) : ZMod n), mem _ ht⟩ := by
    apply Subtype.ext
    change z.val = o + ((a + (j - a) : ℕ) : ZMod n)
    rw [he, Nat.add_sub_of_le haj]
  rw [he']
  exact reach _ ht

private theorem long_strip {V : Type} (G : SimpleGraph V) (S : Set V) (pos : ℕ → V)
    {a b r t : ℕ} (hr : 0 < r) (ht : t < r) (hab : a + r ≤ b)
    (live : ∀ z, a ≤ z → z < b + r → (z - a) % r = t → pos z ∉ S)
    (long : ∀ z, G.Adj (pos z) (pos (z + r))) :
    ∃ u v : ↑(Sᶜ : Set V), u.val = pos (a + t) ∧
      (∃ z, b ≤ z ∧ z < b + r ∧ v.val = pos z) ∧ (G.induce Sᶜ).Reachable u v := by
  let pack (z : ℕ) (h₁ : a ≤ z) (h₂ : z < b + r) (h₃ : (z - a) % r = t) : ↑(Sᶜ : Set V) :=
    ⟨pos z, live z h₁ h₂ h₃⟩
  let rec carry (z : ℕ) (h₁ : a ≤ z) (h₂ : z < b + r) (h₃ : (z - a) % r = t) :
      ∃ v : ↑(Sᶜ : Set V), (∃ w, b ≤ w ∧ w < b + r ∧ v.val = pos w) ∧
        (G.induce Sᶜ).Reachable (pack z h₁ h₂ h₃) v := by
    by_cases hb : b ≤ z
    · exact ⟨pack z h₁ h₂ h₃, ⟨z, hb, h₂, rfl⟩, SimpleGraph.Reachable.rfl⟩
    · have h₃' : (z + r - a) % r = t := by
        rw [show z + r - a = (z - a) + r by omega, Nat.add_mod_right, h₃]
      have h₁' : a ≤ z + r := by omega
      have h₂' : z + r < b + r := by omega
      obtain ⟨v, hv, hreach⟩ := carry (z + r) h₁' h₂' h₃'
      have edge : (G.induce Sᶜ).Adj (pack z h₁ h₂ h₃) (pack (z + r) h₁' h₂' h₃') := long z
      exact ⟨v, hv, edge.reachable.trans hreach⟩
  termination_by b - z
  decreasing_by omega
  have init₁ : a ≤ a + t := by omega
  have init₂ : a + t < b + r := by omega
  have init₃ : (a + t - a) % r = t := by simp [Nat.mod_eq_of_lt ht]
  obtain ⟨v, hv, hreach⟩ := carry (a + t) init₁ init₂ init₃
  exact ⟨pack (a + t) init₁ init₂ init₃, v, rfl, hv, hreach⟩

private theorem two_arcs {n r a b : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (o : ZMod n) (hab : a + r ≤ b) (hb : b + r ≤ n)
    (S : Finset (ZMod n)) (hS : S.card < 2 * r)
    (dA : Disjoint (blockAt o a r) (S : Set (ZMod n)))
    (dB : Disjoint (blockAt o b r) (S : Set (ZMod n))) :
    ∃ u v : ↑((S : Set (ZMod n))ᶜ), u.val ∈ blockAt o a r ∧ v.val ∈ blockAt o b r ∧
      ((cutD n r o).induce ((S : Set (ZMod n))ᶜ)).Reachable u v := by
  classical
  have hr0 : 0 < r := by omega
  let pos (j : ℕ) : ZMod n := o + (j : ZMod n)
  have cycle (j : ℕ) (hj : n ≤ j) : pos j = pos (j - n) := by
    dsimp [pos]
    rw [Nat.cast_sub hj, ZMod.natCast_self, sub_zero]
  let color (x : ZMod n) : Fin (2 * r) :=
    let j := coordinate o x
    if a ≤ j ∧ j < b then ⟨(j - a) % r, by have := Nat.mod_lt (j - a) hr0; omega⟩
    else
      let w := if j < a then j + n else j
      ⟨r + (w - b) % r, by have := Nat.mod_lt (w - b) hr0; omega⟩
  obtain ⟨missing, hmissing⟩ : ∃ i : Fin (2 * r), i ∉ S.image color := by
    by_contra! h
    have hc : (Finset.univ : Finset (Fin (2 * r))).card ≤ (S.image color).card :=
      Finset.card_le_card (fun i _ => h i)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    exact (not_le_of_gt hS) (hc.trans Finset.card_image_le)
  have walk_edge (j : ℕ) : (cutD n r o).Adj (pos j) (pos (j + r)) := by
    simpa only [pos, Nat.cast_add, add_assoc] using long_survives hr hn o (pos j)
  by_cases hlow : missing.val < r
  · let t := missing.val
    have live (z : ℕ) (h₁ : a ≤ z) (h₂ : z < b + r) (h₃ : (z - a) % r = t) :
        pos z ∉ (S : Set (ZMod n)) := by
      intro hz
      by_cases hB : b ≤ z
      · exact Set.disjoint_left.1 dB ⟨z, hB, h₂, rfl⟩ hz
      · have hzcoord := add_index o z (by omega : z < n)
        have hcol : color (pos z) = missing := by
          apply Fin.ext
          change (color (pos z)).val = t
          simp [color, pos, hzcoord, h₁, show z < b by omega, h₃]
        exact hmissing (Finset.mem_image.2 ⟨pos z, hz, hcol⟩)
    obtain ⟨u, v, hu, ⟨z, hz₁, hz₂, hv⟩, hp⟩ :=
      long_strip (cutD n r o) (S : Set (ZMod n)) pos hr0 hlow hab live walk_edge
    exact ⟨u, v, ⟨a + t, by omega, by omega, hu⟩, ⟨z, hz₁, hz₂, hv⟩, hp⟩
  · let t := missing.val - r
    have ht : t < r := by have := missing.isLt; dsimp [t]; omega
    have teq : r + t = missing.val := by dsimp [t]; omega
    have live (z : ℕ) (h₁ : b ≤ z) (h₂ : z < a + n + r) (h₃ : (z - b) % r = t) :
        pos z ∉ (S : Set (ZMod n)) := by
      intro hz
      by_cases hA : a + n ≤ z
      · exact Set.disjoint_left.1 dA ⟨z - n, by omega, by omega, cycle z (by omega)⟩ hz
      · have hcol : color (pos z) = missing := by
          apply Fin.ext
          by_cases hw : z < n
          · have hzcoord := add_index o z hw
            simp [color, pos, hzcoord, show ¬ z < b by omega, show ¬ z < a by omega, h₃, teq]
          · have hcycle := cycle z (by omega)
            have hzcoord := add_index o (z - n) (by omega : z - n < n)
            rw [hcycle]
            have he : z - n + n = z := by omega
            simp [color, pos, hzcoord, show ¬ a ≤ z - n by omega, show z - n < a by omega,
              he, h₃, teq]
        exact hmissing (Finset.mem_image.2 ⟨pos z, hz, hcol⟩)
    obtain ⟨u, v, hu, ⟨z, hz₁, hz₂, hv⟩, hp⟩ :=
      long_strip (cutD n r o) (S : Set (ZMod n)) pos hr0 ht (show b + r ≤ a + n by omega)
        live walk_edge
    refine ⟨v, u, ⟨z - n, by omega, by omega, hv.trans (cycle z (by omega))⟩,
      ⟨b + t, by omega, by omega, hu⟩, hp.symm⟩

private theorem pathwidth_D_short_lower (r n : ℕ) (hr : 2 ≤ r) (hn : 4 * r^2 < n + 2 * r)
    (i : ZMod n) :
    ¬ PwLE ((circulantD n r).deleteEdges {s(i, i + 1)}) (2 * r - 1) := by
  classical
  have mul : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hn' : 2 * r < n := by nlinarith
  have : NeZero n := ⟨by omega⟩
  let o := i + 1
  have he : o - 1 = i := by simp [o]
  change ¬ PwLE ((circulantD n r).deleteEdges {s(i, o)}) (2 * r - 1)
  rw [← he]
  change ¬ PwLE (cutD n r o) (2 * r - 1)
  let a (j : Fin (2 * r + 1)) := r * j.val
  let A (j : Fin (2 * r + 1)) := blockAt o (a j) r
  have fit (j : Fin (2 * r + 1)) : a j + r ≤ n := by
    have hj : j.val + 1 ≤ 2 * r + 1 := j.isLt
    have hl := Nat.mul_le_mul_left r hj
    dsimp [a]
    nlinarith
  have order {j k : Fin (2 * r + 1)} (h : j < k) : a j + r ≤ a k := by
    have h' := Nat.mul_le_mul_left r (show j.val + 1 ≤ k.val from h)
    simpa only [a, Nat.mul_add, Nat.mul_one] using h'
  have disj : ∀ j k, j ≠ k → Disjoint (A j) (A k) := by
    have before (j k : Fin (2 * r + 1)) (h : j < k) : Disjoint (A j) (A k) := by
      refine Set.disjoint_left.2 ?_
      rintro v ⟨x, hx₁, hx₂, hvx⟩ ⟨y, hy₁, hy₂, hvy⟩
      have heq := congrArg (coordinate o) (hvx.symm.trans hvy)
      rw [add_index o x (by have := fit j; omega), add_index o y (by have := fit k; omega)] at heq
      have := order h
      omega
    intro j k hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact before j k h
    · exact (before k j h).symm
  apply pathwidth_disjoint_blocks (cutD n r o) A (2 * r) (by omega) (by simp)
    (fun j => block_connected hr hn' o (fit j)) disj
  intro j k hne S hS dj dk
  rcases lt_or_gt_of_ne hne with h | h
  · exact two_arcs hr hn' o (order h) (fit k) S hS dj dk
  · obtain ⟨v, u, hv, hu, hp⟩ := two_arcs hr hn' o (order h) (fit j) S hS dk dj
    exact ⟨u, v, hu, hv, hp.symm⟩

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Use two alternating families of bags for the two vertex types of the split graph.

private theorem pathwidth_of_injection {V W : Type} [Finite V] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f) (map_adj : ∀ x y, G.Adj x y → H.Adj (f x) (f y))
    {k : ℕ} (h : PwLE H k) : PwLE G k := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨s, B, ⟨hs, hedges, hverts, hinterval⟩, hsize⟩ := h
  let U : Fin s → Finset V := fun t => Finset.univ.filter fun x => f x ∈ B t
  have mem (t : Fin s) (x : V) : x ∈ U t ↔ f x ∈ B t := by simp [U]
  refine ⟨s, U, ⟨hs, ?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨t, ht, ht'⟩ := hedges _ _ (map_adj x y hxy)
    exact ⟨t, (mem t x).2 ht, (mem t y).2 ht'⟩
  · intro x
    obtain ⟨t, ht⟩ := hverts (f x)
    exact ⟨t, (mem _ _).2 ht⟩
  · intro x i j l hij hjl hxi hxl
    exact (mem _ _).2 (hinterval _ _ _ _ hij hjl ((mem _ _).1 hxi) ((mem _ _).1 hxl))
  · intro t
    exact (Finset.card_le_card_of_injOn f (fun x hx => (mem _ _).1 hx) hf.injOn).trans (hsize t)

private theorem pathwidth_monotone {V : Type} [Finite V] {G H : SimpleGraph V} (hGH : G ≤ H)
    {k : ℕ} (h : PwLE H k) : PwLE G k :=
  pathwidth_of_injection id Function.injective_id (fun _ _ he => hGH he) h

private theorem pathwidth_bipartite_linear {V : Type} [Finite V] (G : SimpleGraph V)
    (isU : V → Bool) (f : V → ℕ) (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
    (inj : ∀ x y, isU x = isU y → f x = f y → x = y) (fits : ∀ x, f x < s)
    (edges : ∀ x y, G.Adj x y →
      (isU x = true ∧ isU y = false ∧ f y ≤ f x ∧ f x ≤ f y + r) ∨
      (isU y = true ∧ isU x = false ∧ f x ≤ f y ∧ f y ≤ f x + r)) :
    PwLE G r := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let lo (x : V) := if isU x then 2 * f x else 2 * f x + 1
  let hi (x : V) := if isU x then 2 * f x + 1 else 2 * (f x + r)
  let W : Fin (2 * s) → Finset V :=
    fun t => Finset.univ.filter fun x => lo x ≤ t.val ∧ t.val ≤ hi x
  have mem (x : V) (t : Fin (2 * s)) : x ∈ W t ↔ lo x ≤ t.val ∧ t.val ≤ hi x := by simp [W]
  have edge_bag (x y : V) (hu : isU x = true) (hv : isU y = false)
      (h₁ : f y ≤ f x) (h₂ : f x ≤ f y + r) :
      ∃ t, x ∈ W t ∧ y ∈ W t := by
    by_cases he : f x = f y
    · let t : Fin (2 * s) := ⟨2 * f x + 1, by have := fits x; omega⟩
      refine ⟨t, (mem _ _).2 ?_, (mem _ _).2 ?_⟩
      all_goals simp [lo, hi, hu, hv, t, he] <;> omega
    · let t : Fin (2 * s) := ⟨2 * f x, by have := fits x; omega⟩
      refine ⟨t, (mem _ _).2 ?_, (mem _ _).2 ?_⟩
      all_goals simp [lo, hi, hu, hv, t] <;> omega
  refine ⟨2 * s, W, ⟨by omega, ?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    rcases edges x y hxy with ⟨hu, hv, h₁, h₂⟩ | ⟨hu, hv, h₁, h₂⟩
    · exact edge_bag x y hu hv h₁ h₂
    · obtain ⟨t, hy, hx⟩ := edge_bag y x hu hv h₁ h₂
      exact ⟨t, hx, hy⟩
  · intro x
    have hlt : lo x < 2 * s := by
      have := fits x
      cases h : isU x <;> simp [lo, h] <;> omega
    refine ⟨⟨lo x, hlt⟩, (mem _ _).2 ⟨le_rfl, ?_⟩⟩
    show lo x ≤ hi x
    cases h : isU x <;> simp [lo, hi, h] <;> omega
  · intro x i j k hij hjk hxi hxk
    exact (mem _ _).2 ⟨((mem _ _).1 hxi).1.trans (show i.val ≤ j.val from hij),
      (show j.val ≤ k.val from hjk).trans ((mem _ _).1 hxk).2⟩
  · intro t
    let left := (W t).filter fun x => isU x = true
    let right := (W t).filter fun x => isU x = false
    have hsum : left.card + right.card = (W t).card := by
      have hdisj : Disjoint left right := by
        refine Finset.disjoint_left.2 ?_
        intro x hx hy
        have hxu := (Finset.mem_filter.1 hx).2
        have hxv := (Finset.mem_filter.1 hy).2
        simp [hxu] at hxv
      have hUnion : left ∪ right = W t := by
        ext x
        cases eh : isU x <;> simp [left, right, eh]
      rw [← Finset.card_union_of_disjoint hdisj, hUnion]
    have hleft : left.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      obtain ⟨hxW, hxU⟩ := Finset.mem_filter.1 hx
      obtain ⟨hyW, hyU⟩ := Finset.mem_filter.1 hy
      have hx' := (mem x t).1 hxW
      have hy' := (mem y t).1 hyW
      simp [lo, hi, hxU, hyU] at hx' hy'
      exact inj x y (hxU.trans hyU.symm) (by omega)
    let indices := Finset.Icc ((t.val + 1) / 2 - r) ((t.val - 1) / 2)
    have maps : (right.card ≤ indices.card) := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        obtain ⟨hxW, hxU⟩ := Finset.mem_filter.1 (show x ∈ right from hx)
        have h := (mem x t).1 hxW
        simp [lo, hi, hxU] at h
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
      · intro x hx y hy h
        exact inj x y ((Finset.mem_filter.1 (show x ∈ right from hx)).2.trans
          (Finset.mem_filter.1 (show y ∈ right from hy)).2.symm) h
    have hrange : indices.card ≤ r := by
      dsimp [indices]
      rw [Nat.card_Icc]
      omega
    omega

private theorem splitB_step_iff {n r : ℕ} (j i : ZMod n) :
    (splitB n r).Adj (Sum.inr j) (Sum.inl i) ↔
    ∃ k : ℕ, (k = 0 ∨ k = 1 ∨ k = r) ∧ i = j + (k : ZMod n) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem splitB_not_inl_inl {n r : ℕ} (x y : ZMod n) :
    ¬ (splitB n r).Adj (Sum.inl x) (Sum.inl y) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem splitB_not_inr_inr {n r : ℕ} (x y : ZMod n) :
    ¬ (splitB n r).Adj (Sum.inr x) (Sum.inr y) := by
  simp [splitB, SimpleGraph.fromRel_adj, splitRel]

private theorem pathwidth_split_order {n r s : ℕ} [NeZero n] (hs : 0 < s) (hr : 0 < r)
    {G : SimpleGraph (ZMod n ⊕ ZMod n)} (hle : G ≤ splitB n r) (T : Set (ZMod n ⊕ ZMod n))
    (u v : ZMod n → ℕ) (hu : Function.Injective u) (hv : Function.Injective v)
    (huFit : ∀ x, u x < s) (hvFit : ∀ x, v x < s)
    (linear : ∀ x y, Sum.inr x ∈ T → Sum.inl y ∈ T →
      G.Adj (Sum.inr x) (Sum.inl y) → v x ≤ u y ∧ u y ≤ v x + r) :
    PwLE (G.induce T) r := by
  apply pathwidth_bipartite_linear _ (fun x : T => x.val.elim (fun _ => true) (fun _ => false))
    (fun x : T => x.val.elim u v) s r hs hr
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hUV hf
    cases x <;> cases y
    · exact Subtype.ext (congrArg Sum.inl (hu hf))
    · cases hUV
    · cases hUV
    · exact Subtype.ext (congrArg Sum.inr (hv hf))
  · rintro ⟨x | x, hx⟩
    · exact huFit x
    · exact hvFit x
  · rintro ⟨x | x, hx⟩ ⟨y | y, hy⟩ he
    · exact (splitB_not_inl_inl _ _ (hle he)).elim
    · exact .inl ⟨rfl, rfl, linear y x hy hx (SimpleGraph.induce_adj.mp he).symm⟩
    · exact .inr ⟨rfl, rfl, linear x y hx hy he⟩
    · exact (splitB_not_inr_inr _ _ (hle he)).elim

private def uWindow {n : ℕ} (o : ZMod n) (F : Finset ℕ) : Set (ZMod n ⊕ ZMod n) :=
  {x | x.elim (fun j => coordinate o j ∈ F) (fun _ => False)}

private theorem uWindow_card {n : ℕ} [NeZero n] (o : ZMod n) (F : Finset ℕ) :
    (uWindow o F).ncard ≤ F.card := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  let f : ZMod n ⊕ ZMod n → ℕ := Sum.elim (coordinate o) (fun _ => 0)
  have hu (x : ZMod n ⊕ ZMod n) (hx : x ∈ (uWindow o F).toFinite.toFinset) :
      x ∈ uWindow o F := by simpa [uWindow] using hx
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    have h := hu x hx
    cases x with
    | inl x => exact h
    | inr x => exact (show False from h).elim
  · intro x hx y hy he
    have h₁ := hu x hx
    have h₂ := hu y hy
    cases x <;> cases y
    · exact congrArg Sum.inl (coordinate_injective o he)
    · exact (show False from h₂).elim
    · exact (show False from h₁).elim
    · exact (show False from h₁).elim

private theorem pathwidth_B_delete_u {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (o : ZMod n) :
    PwLE ((splitB n r).induce (uWindow o (Finset.range r))ᶜ) r := by
  have : NeZero n := ⟨by omega⟩
  apply pathwidth_split_order (by omega : 0 < n) (by omega : 0 < r)
    (le_refl _) _ (coordinate o) (coordinate o)
    (coordinate_injective o) (coordinate_injective o) (coordinate_lt o) (coordinate_lt o)
  intro x y hx hy he
  obtain ⟨k, hk, hh⟩ := (splitB_step_iff _ _).1 he
  have hk' : k ≤ r := by rcases hk with rfl | rfl | rfl <;> omega
  have hs := coordinate_step o x k (by omega : k < n)
  rw [← hh] at hs
  rcases hs with hs | hs
  · omega
  · have hny : coordinate o y ∉ Finset.range r := hy
    rw [Finset.mem_range] at hny
    have := coordinate_lt o x
    omega

private def flipB {n : ℕ} : (ZMod n ⊕ ZMod n) → (ZMod n ⊕ ZMod n)
  | .inl x => .inr (-x)
  | .inr x => .inl (-x)

private theorem flipB_invol {n : ℕ} : Function.Involutive (@flipB n) := by
  rintro (x | x) <;> simp [flipB]

private theorem flipB_adj {n r : ℕ} (x y : ZMod n ⊕ ZMod n) (he : (splitB n r).Adj x y) :
    (splitB n r).Adj (flipB x) (flipB y) := by
  have step (i j : ZMod n) (h : (splitB n r).Adj (Sum.inr j) (Sum.inl i)) :
      (splitB n r).Adj (Sum.inr (-i)) (Sum.inl (-j)) := by
    obtain ⟨k, hk, h⟩ := (splitB_step_iff _ _).1 h
    exact (splitB_step_iff _ _).2 ⟨k, hk, by linear_combination h⟩
  cases x <;> cases y
  · exact (splitB_not_inl_inl _ _ he).elim
  · exact step _ _ he.symm
  · exact (step _ _ he).symm
  · exact (splitB_not_inr_inr _ _ he).elim

private theorem pathwidth_B_local_delete {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n)
    (x : ZMod n ⊕ ZMod n) :
    ∃ U : Set (ZMod n ⊕ ZMod n), x ∈ U ∧ U.ncard ≤ r ∧ PwLE ((splitB n r).induce Uᶜ) r := by
  classical
  have : NeZero n := ⟨by omega⟩
  have blockCard (o : ZMod n) : (uWindow o (Finset.range r)).ncard ≤ r := by
    simpa using uWindow_card o (Finset.range r)
  have first (o : ZMod n) : Sum.inl o ∈ uWindow o (Finset.range r) := by
    change coordinate o o ∈ Finset.range r
    simp [coordinate]
    omega
  cases x with
  | inl x =>
    exact ⟨uWindow x (Finset.range r), first x, blockCard x, pathwidth_B_delete_u hr hn x⟩
  | inr x =>
    let U := uWindow (-x) (Finset.range r)
    let T := flipB ⁻¹' U
    refine ⟨T, first (-x), ?_, ?_⟩
    · calc
        T.ncard ≤ U.ncard := Set.ncard_le_ncard_of_injOn flipB (fun _ hx => hx) flipB_invol.injective.injOn
        _ ≤ r := blockCard (-x)
    · let f : ↑(Tᶜ : Set (ZMod n ⊕ ZMod n)) → ↑(Uᶜ : Set (ZMod n ⊕ ZMod n)) :=
        fun z => ⟨flipB z.val, z.property⟩
      have hf : Function.Injective f := fun a b h => Subtype.ext
        (flipB_invol.injective (congrArg Subtype.val h))
      exact pathwidth_of_injection f hf (fun _ _ he => flipB_adj _ _ he)
        (pathwidth_B_delete_u hr hn (-x))

private theorem pathwidth_B_delete_long {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (i : ZMod n) :
    PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + (r : ZMod n)))}) (2 * r - 1) := by
  have : NeZero n := ⟨by omega⟩
  let o := i + 1
  let U := uWindow o (Finset.range (r - 1))
  let G := (splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + (r : ZMod n)))}
  have cardU : U.ncard ≤ r - 1 := by simpa [U] using uWindow_card o (Finset.range (r - 1))
  have bound : PwLE (G.induce Uᶜ) r := by
    have hle : G ≤ splitB n r := fun _ _ h => (SimpleGraph.deleteEdges_adj.1 h).1
    apply pathwidth_split_order (by omega : 0 < n) (by omega : 0 < r) hle _
      (coordinate o) (coordinate o) (coordinate_injective o) (coordinate_injective o)
      (coordinate_lt o) (coordinate_lt o)
    intro x y hx hy hxy
    obtain ⟨k, hk, hh⟩ := (splitB_step_iff _ _).1 (hle hxy)
    have hk' : k ≤ r := by rcases hk with rfl | rfl | rfl <;> omega
    have hs := coordinate_step o x k (by omega : k < n)
    rw [← hh] at hs
    rcases hs with hs | hs
    · omega
    · have hny : coordinate o y ∉ Finset.range (r - 1) := hy
      rw [Finset.mem_range] at hny
      have hxn := coordinate_lt o x
      have hx' : coordinate o x = n - 1 := by omega
      have hk'' : k = r := by omega
      have ex : x = i := by
        rw [← coordinate_spec o x, hx', Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
        simp [o]
      have ey : y = i + (r : ZMod n) := by rw [hh, ex, hk'']
      exfalso
      exact (SimpleGraph.deleteEdges_adj.1 hxy).2 (by rw [ex, ey]; exact Set.mem_singleton _)
  convert pathwidth_add_vertices G U r (r - 1) cardU bound using 1 <;> omega

private theorem pathwidth_B_delete_spoke {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (i : ZMod n) :
    PwLE ((splitB n r).deleteEdges {s(Sum.inl i, Sum.inr i)}) (2 * r - 1) := by
  have : NeZero n := ⟨by omega⟩
  let U := uWindow i (Finset.Ico 1 r)
  let G := (splitB n r).deleteEdges {s(Sum.inl i, Sum.inr i)}
  let u (x : ZMod n) := if coordinate i x = 0 then n else coordinate i x
  have cardU : U.ncard ≤ r - 1 := by simpa [U, Nat.card_Ico] using uWindow_card i (Finset.Ico 1 r)
  have inj : Function.Injective u := by
    intro x y he
    apply coordinate_injective i
    have hx := coordinate_lt i x
    have hy := coordinate_lt i y
    dsimp [u] at he
    split at he <;> split at he <;> omega
  have bound : PwLE (G.induce Uᶜ) r := by
    have hle : G ≤ splitB n r := fun _ _ h => (SimpleGraph.deleteEdges_adj.1 h).1
    apply pathwidth_split_order (by omega : 0 < n + 1) (by omega : 0 < r) hle _
      u (coordinate i) inj (coordinate_injective i)
    · intro x
      have := coordinate_lt i x
      dsimp [u]
      split <;> omega
    · intro x
      have := coordinate_lt i x
      omega
    · intro x y hx hy hxy
      obtain ⟨k, hk, hh⟩ := (splitB_step_iff _ _).1 (hle hxy)
      have hk' : k ≤ r := by rcases hk with rfl | rfl | rfl <;> omega
      have hs := coordinate_step i x k (by omega : k < n)
      rw [← hh] at hs
      have hxb := coordinate_lt i x
      have hny : coordinate i y ∉ Finset.Ico 1 r := hy
      rw [Finset.mem_Ico] at hny
      dsimp [u]
      by_cases hz : coordinate i y = 0
      · rw [if_pos hz]
        rcases hs with hs | hs
        · have hxz : coordinate i x = 0 := by omega
          have ex : x = i := by rw [← coordinate_spec i x, hxz, Nat.cast_zero, add_zero]
          have ey : y = i := by rw [← coordinate_spec i y, hz, Nat.cast_zero, add_zero]
          exfalso
          exact (SimpleGraph.deleteEdges_adj.1 hxy.symm).2 (by rw [ex, ey]; exact Set.mem_singleton _)
        · omega
      · rw [if_neg hz]
        omega
  convert pathwidth_add_vertices G U r (r - 1) cardU bound using 1 <;> omega

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Use the pathwidth bounds to cover all vertices and force the cycle-edge correspondence.

private theorem pathwidth_minor_monotone {V W : Type} [Finite W]
    {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}
    (h : HadwigerConj.IsMinor H G) (hG : PwLE G k) : PwLE H k := by
  classical
  let : Fintype W := Fintype.ofFinite W
  obtain ⟨M, hconn, hdisj, hadj⟩ := h
  obtain ⟨s, A, d, bound⟩ := hG
  let B : Fin s → Finset W := fun i => Finset.univ.filter fun w => Touches A (M w) i
  have mem (i : Fin s) (w : W) : w ∈ B i ↔ Touches A (M w) i := by simp [B]
  refine ⟨s, B, ⟨d.1, ?_, ?_, ?_⟩, ?_⟩
  · intro w w' hww'
    obtain ⟨u, hu, v, hv, huv⟩ := hadj _ _ hww'
    obtain ⟨i, hui, hvi⟩ := d.2.1 _ _ huv
    exact ⟨i, (mem _ _).2 ⟨u, hu, hui⟩, (mem _ _).2 ⟨v, hv, hvi⟩⟩
  · intro w
    obtain ⟨u⟩ := (hconn w).nonempty
    obtain ⟨i, hui⟩ := d.2.2.1 u.val
    exact ⟨i, (mem _ _).2 ⟨u.val, u.property, hui⟩⟩
  · intro w i j k hij hjk hi hk
    exact (mem _ _).2 (touches_interval d (hconn w) hij hjk ((mem _ _).1 hi) ((mem _ _).1 hk))
  · intro i
    have hchoice (w : B i) : ∃ v, v ∈ M w.val ∧ v ∈ A i := (mem _ _).1 w.property
    choose f hM hA using hchoice
    have inj : Function.Injective f := by
      intro w w' eq
      apply Subtype.ext
      by_contra! hne
      exact Set.disjoint_left.1 (hdisj _ _ hne) (hM w) (eq.symm ▸ hM w')
    have hcard : (B i).attach.card ≤ (A i).card :=
      Finset.card_le_card_of_injOn f (fun w _ => hA w) inj.injOn
    rw [Finset.card_attach] at hcard
    exact hcard.trans (bound i)

private theorem pathwidth_weaken {V : Type} {G : SimpleGraph V} {j k : ℕ} (hjk : j ≤ k)
    (h : PwLE G j) : PwLE G k := by
  obtain ⟨s, W, d, hb⟩ := h
  exact ⟨s, W, d, fun t => (hb t).trans (Nat.succ_le_succ hjk)⟩

private theorem pathwidth_model_cover {VH VL : Type} [Finite VH] [Finite VL]
    (H : SimpleGraph VH) (L : SimpleGraph VL) (r : ℕ) (hr : 0 < r)
    (hwide : ¬ PwLE H (2 * r - 1))
    (hcut : ∀ v, ∃ U : Set VL, v ∈ U ∧ U.ncard ≤ r ∧ PwLE (L.induce Uᶜ) r)
    (M : VH → Set VL) (hconn : ∀ h, (L.induce (M h)).Connected)
    (hdisj : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hedge : ∀ h h', H.Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', L.Adj u v) :
    ∀ v, ∃ h, v ∈ M h := by
  classical
  intro a
  by_contra! ha
  obtain ⟨U, haU, hUr, hUL⟩ := hcut a
  let S : Set VH := {h | ∃ v ∈ M h, v ∈ U}
  choose p hpM hpU using fun h : S => h.property
  let f (h : VH) : VL := if hS : h ∈ S then p ⟨h, hS⟩ else a
  have hS : S.ncard ≤ r - 1 := by
    have hmap : ∀ h ∈ S, f h ∈ U \ {a} := by
      intro h hh
      rw [show f h = p ⟨h, hh⟩ by simp [f, hh]]
      refine ⟨hpU _, ?_⟩
      intro eq
      exact ha h ((Set.mem_singleton_iff.1 eq) ▸ hpM ⟨h, hh⟩)
    have hinj : Set.InjOn f S := by
      intro h hh h' hh' e
      by_contra! hne
      have ep : p ⟨h, hh⟩ = p ⟨h', hh'⟩ := by simpa [f, hh, hh'] using e
      exact Set.disjoint_left.1 (hdisj _ _ hne) (hpM ⟨h, hh⟩) (ep.symm ▸ hpM ⟨h', hh'⟩)
    have hc := Set.ncard_le_ncard_of_injOn f hmap hinj
    rw [Set.ncard_sdiff_singleton_of_mem haU] at hc
    omega
  have avoid (h : VH) (hh : h ∉ S) : Disjoint (M h) U :=
    Set.disjoint_left.2 fun x hx hu => hh ⟨x, hx, hu⟩
  have hm := minor_avoid_deleted_vertices L H M hconn hdisj hedge U S avoid
  have hsub := pathwidth_minor_monotone hm hUL
  have hall := pathwidth_add_vertices H S r (r - 1) hS hsub
  exact hwide (pathwidth_weaken (by omega) hall)

private theorem minor_delete_crossing {VH VL : Type} {H K : SimpleGraph VH} (hKH : K ≤ H)
    {L : SimpleGraph VL} {M : VH → Set VL}
    (hconn : ∀ h, (L.induce (M h)).Connected)
    (hdisj : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hedge : ∀ h h', H.Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', L.Adj u v)
    {lab : VL → VH} (hlab : ∀ v, v ∈ M (lab v)) (a b : VL) (hab : lab a ≠ lab b)
    (alt : K.Adj (lab a) (lab b) →
      ∃ x ∈ M (lab a), ∃ y ∈ M (lab b), L.Adj x y ∧ s(x, y) ≠ s(a, b)) :
    HadwigerConj.IsMinor K (L.deleteEdges {s(a, b)}) := by
  classical
  have unique {v : VL} {h : VH} (hv : v ∈ M h) : lab v = h := by
    by_contra! hne
    exact Set.disjoint_left.1 (hdisj _ _ hne) (hlab v) hv
  refine ⟨M, ?_, hdisj, ?_⟩
  · intro h
    apply (hconn h).mono
    intro u v huv
    change L.Adj u.val v.val at huv
    change (L.deleteEdges {s(a, b)}).Adj u.val v.val
    refine SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩
    intro hdel
    rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hdel) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hab ((unique (h₁ ▸ u.property)).trans (unique (h₂ ▸ v.property)).symm)
    · exact hab ((unique (h₂ ▸ v.property)).trans (unique (h₁ ▸ u.property)).symm)
  · have alt' (k : K.Adj (lab a) (lab b)) :
        ∃ x ∈ M (lab a), ∃ y ∈ M (lab b), (L.deleteEdges {s(a, b)}).Adj x y := by
      obtain ⟨x, hx, y, hy, hxy, hne⟩ := alt k
      exact ⟨x, hx, y, hy, SimpleGraph.deleteEdges_adj.2 ⟨hxy, hne⟩⟩
    intro h h' hh'
    obtain ⟨u, hu, v, hv, huv⟩ := hedge h h' (hKH hh')
    by_cases he : s(u, v) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← unique hu, ← unique hv] at hh' ⊢
        exact alt' hh'
      · rw [← unique hu, ← unique hv] at hh' ⊢
        obtain ⟨x, hx, y, hy, he⟩ := alt' hh'.symm
        exact ⟨y, hy, x, hx, he.symm⟩
    · exact ⟨u, hu, v, hv, SimpleGraph.deleteEdges_adj.2 ⟨huv, he⟩⟩

private theorem pathwidth_model_rigid {VH VL : Type} [Finite VH] [Finite VL]
    (H : SimpleGraph VH) (L : SimpleGraph VL) (r : ℕ) (hr : 0 < r)
    (CH : Set (Sym2 VH)) (CL : Set (Sym2 VL))
    (hwide : ¬ PwLE H (2 * r - 1))
    (hrobust : ∀ f ∈ H.edgeSet, f ∉ CH → ¬ PwLE (H.deleteEdges {f}) (2 * r - 1))
    (hcut : ∀ v, ∃ U : Set VL, v ∈ U ∧ U.ncard ≤ r ∧ PwLE (L.induce Uᶜ) r)
    (hthin : ∀ e ∈ CL, PwLE (L.deleteEdges {e}) (2 * r - 1))
    (M : VH → Set VL) (hconn : ∀ h, (L.induce (M h)).Connected)
    (hdisj : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hedge : ∀ h h', H.Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', L.Adj u v) :
    ∃ lab : VL → VH, (∀ v, v ∈ M (lab v)) ∧
      ∀ a b, s(a, b) ∈ CL → lab a ≠ lab b →
        s(lab a, lab b) ∈ CH ∧
          ∀ x y, L.Adj x y → s(lab x, lab y) = s(lab a, lab b) → s(x, y) = s(a, b) := by
  classical
  choose lab hlabel using pathwidth_model_cover H L r hr hwide hcut M hconn hdisj hedge
  refine ⟨lab, hlabel, ?_⟩
  intro a b he hab
  have modl {K : SimpleGraph VH} (hk : K ≤ H)
      (alt : K.Adj (lab a) (lab b) →
        ∃ x ∈ M (lab a), ∃ y ∈ M (lab b), L.Adj x y ∧ s(x, y) ≠ s(a, b)) :
      PwLE K (2 * r - 1) :=
    pathwidth_minor_monotone (minor_delete_crossing hk hconn hdisj hedge hlabel a b hab alt)
      (hthin _ he)
  have hadj : H.Adj (lab a) (lab b) := by
    by_contra! h
    exact hwide (modl (le_refl _) (fun hh => (h hh).elim))
  refine ⟨?_, ?_⟩
  · by_contra! h
    have hrob := hrobust _ ((SimpleGraph.mem_edgeSet H).2 hadj) h
    apply hrob (modl (SimpleGraph.deleteEdges_le _) ?_)
    intro hh
    exact ((SimpleGraph.deleteEdges_adj.1 hh).2 (Set.mem_singleton _)).elim
  · intro x y hxy h
    by_contra! hne
    apply hwide (modl (le_refl _) ?_)
    intro _
    rcases Sym2.eq_iff.1 h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨x, hx ▸ hlabel x, y, hy ▸ hlabel y, hxy, hne⟩
    · have nn : s(y, x) ≠ s(a, b) :=
        fun eq => hne ((Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)).trans eq)
      exact ⟨y, hy ▸ hlabel y, x, hx ▸ hlabel x, hxy.symm, nn⟩

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Contract the spokes for the split lower bound and apply the rigidity lemma to both families.

private theorem swap_edge_eq {V : Type} (x y : V) : s(x, y) = s(y, x) :=
  Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)

private theorem one_step_ne {n : ℕ} (hn : 1 < n) (i : ZMod n) : i ≠ i + 1 := by
  intro h
  have he : ((1 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination -h
  have h' := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hn, ZMod.val_zero] at h'
  omega

private theorem splitB_contract_spokes {n r : ℕ} (hn : 2 * r < n) (hr : 2 ≤ r) (i : ZMod n) :
    HadwigerConj.IsMinor ((circulantD n r).deleteEdges {s(i, i + 1)})
      ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + 1))}) := by
  let M (h : ZMod n) : Set (ZMod n ⊕ ZMod n) := {x | x = Sum.inl h ∨ x = Sum.inr h}
  let G := (splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + 1))}
  have spoke (x : ZMod n) : G.Adj (Sum.inr x) (Sum.inl x) := by
    refine SimpleGraph.deleteEdges_adj.2 ⟨(splitB_step_iff _ _).2 ⟨0, .inl rfl, by simp⟩, ?_⟩
    intro e
    rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 e) with ⟨e₁, e₂⟩ | ⟨e₁, _⟩
    · have h₁ := Sum.inr.inj e₁
      have h₂ := Sum.inl.inj e₂
      exact one_step_ne (by omega) i (h₁.symm.trans h₂)
    · cases e₁
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
    refine ⟨⟨Sum.inr x, Or.inr rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    rcases hz with he | he
    · subst z
      exact SimpleGraph.Adj.reachable (spoke x)
    · subst z
      exact SimpleGraph.Reachable.rfl
  · intro x y hne
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    rcases hz with a | a <;> rcases hz' with b | b
    · exact hne (Sum.inl.inj (a.symm.trans b))
    · cases a.symm.trans b
    · cases a.symm.trans b
    · exact hne (Sum.inr.inj (a.symm.trans b))
  · intro x y hxy
    obtain ⟨hD, hshort⟩ := SimpleGraph.deleteEdges_adj.1 hxy
    obtain ⟨k, hk, he⟩ := circulant_adj_oriented hD
    have edge (u v : ZMod n) (hs : s(u, v) ∉ ({s(i, i + 1)} : Set (Sym2 (ZMod n))))
        (heq : v = u + (k : ZMod n)) : G.Adj (Sum.inr u) (Sum.inl v) := by
      have hB := (splitB_step_iff u v).2 ⟨k, .inr hk, heq⟩
      refine SimpleGraph.deleteEdges_adj.2 ⟨hB, ?_⟩
      intro hbad
      rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 hbad) with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
      · apply hs
        simpa only [Sum.inr.inj h₁, Sum.inl.inj h₂] using (Set.mem_singleton (s(i, i + 1)))
      · cases h₁
    rcases he with he | he
    · exact ⟨Sum.inr x, Or.inr rfl, Sum.inl y, Or.inl rfl, edge x y hshort he⟩
    · have hs : s(y, x) ∉ ({s(i, i + 1)} : Set (Sym2 (ZMod n))) := by
        rw [swap_edge_eq y x]
        exact hshort
      exact ⟨Sum.inl x, Or.inl rfl, Sum.inr y, Or.inr rfl, (edge y x hs he).symm⟩

private theorem pathwidth_B_short_lower (r n : ℕ) (hr : 2 ≤ r) (hn : 4 * r^2 < n + 2 * r)
    (i : ZMod n) :
    ¬ PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + 1))}) (2 * r - 1) := by
  have hmul : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hn' : 2 * r < n := by nlinarith
  have : NeZero n := ⟨by omega⟩
  intro h
  exact pathwidth_D_short_lower r n hr hn i
    (pathwidth_minor_monotone (splitB_contract_spokes hn' hr i) h)

private def cycleStepB {n : ℕ} (r : ℕ) : ZMod n ⊕ ZMod n → ZMod n ⊕ ZMod n
  | Sum.inl x => Sum.inr x
  | Sum.inr x => Sum.inl (x + (r : ZMod n))

private def cycleEdgesOf {V : Type} (next : V → V) : Set (Sym2 V) :=
  Set.range fun v => s(v, next v)

private theorem cycle_edge_cases_D {n r : ℕ} {x y : ZMod n} (h : (circulantD n r).Adj x y) :
    s(x, y) ∈ cycleEdgesOf (fun z : ZMod n => z + (r : ZMod n)) ∨
    ∃ i : ZMod n, s(x, y) = s(i, i + 1) := by
  obtain ⟨k, hk, he⟩ := circulant_adj_oriented h
  rcases hk with rfl | rfl
  · right
    rcases he with he | he
    · exact ⟨x, by simp [he]⟩
    · exact ⟨y, by simpa [he] using swap_edge_eq x y⟩
  · left
    rcases he with he | he
    · exact ⟨x, congrArg (fun z => s(x, z)) he.symm⟩
    · exact ⟨y, (congrArg (fun z => s(y, z)) he.symm).trans (swap_edge_eq _ _)⟩

private theorem cycle_edge_cases_B {n r : ℕ} {x y : ZMod n ⊕ ZMod n} (h : (splitB n r).Adj x y) :
    s(x, y) ∈ cycleEdgesOf (@cycleStepB n r) ∨
    ∃ i : ZMod n, s(x, y) = s(Sum.inr i, Sum.inl (i + 1)) := by
  have f (i j : ZMod n) (he : (splitB n r).Adj (Sum.inr i) (Sum.inl j)) :
      s(Sum.inr i, Sum.inl j) ∈ cycleEdgesOf (@cycleStepB n r) ∨
        ∃ a : ZMod n, s(Sum.inr i, Sum.inl j) = s(Sum.inr a, Sum.inl (a + 1)) := by
    obtain ⟨k, hk, hstep⟩ := (splitB_step_iff _ _).1 he
    rcases hk with rfl | rfl | rfl
    · have hji : j = i := by simpa using hstep
      exact .inl ⟨Sum.inl i, by
        change s(Sum.inl i, Sum.inr i) = s(Sum.inr i, Sum.inl j)
        rw [hji]
        exact swap_edge_eq _ _⟩
    · exact .inr ⟨i, by simp [hstep]⟩
    · exact .inl ⟨Sum.inr i, congrArg (fun z => s(Sum.inr i, Sum.inl z)) hstep.symm⟩
  cases x <;> cases y
  · exact (splitB_not_inl_inl _ _ h).elim
  · rw [swap_edge_eq]
    exact f _ _ h.symm
  · exact f _ _ h
  · exact (splitB_not_inr_inr _ _ h).elim

private theorem pathwidth_D_local_delete {n r : ℕ} (hr : 2 ≤ r) (hn : 2 * r < n) (x : ZMod n) :
    ∃ U : Set (ZMod n), x ∈ U ∧ U.ncard ≤ r ∧ PwLE ((circulantD n r).induce Uᶜ) r := by
  classical
  have : NeZero n := ⟨by omega⟩
  let U : Set (ZMod n) := {y | ∃ j < r, y = x + (j : ZMod n)}
  refine ⟨U, ⟨0, by omega, by simp⟩, ?_, (pathwidth_D_upper r n hr hn).2.1 x⟩
  rw [Set.ncard_eq_toFinset_card, ← Finset.card_range r]
  apply Finset.card_le_card_of_injOn (coordinate x) _ (coordinate_injective x).injOn
  intro y hy
  have h : y ∈ U := by simpa [U] using hy
  obtain ⟨j, hj, rfl⟩ := h
  simp [coordinate, add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega : j < n), hj]

private theorem model_D_rigid {r q N : ℕ} (hr : 2 ≤ r) (hq : 4 * r^2 < q + 2 * r) (hN : q ≤ N)
    (M : ZMod q → Set (ZMod N)) (hconn : ∀ h, ((circulantD N r).induce (M h)).Connected)
    (hdisj : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hedge : ∀ h h', (circulantD q r).Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', (circulantD N r).Adj u v) :
    ∃ lab : ZMod N → ZMod q, (∀ v, v ∈ M (lab v)) ∧
      ∀ a b,
        s(a, b) ∈ cycleEdgesOf (fun z : ZMod N => z + (r : ZMod N)) → lab a ≠ lab b →
          s(lab a, lab b) ∈ cycleEdgesOf (fun z : ZMod q => z + (r : ZMod q)) ∧
          ∀ x y, (circulantD N r).Adj x y → s(lab x, lab y) = s(lab a, lab b) → s(x, y) = s(a, b) := by
  have hm : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hq' : 2 * r < q := by nlinarith
  have hN' : 2 * r < N := by omega
  have : NeZero q := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  apply pathwidth_model_rigid (circulantD q r) (circulantD N r) r (by omega) _ _ ?_ ?_
    (pathwidth_D_local_delete hr hN') ?_ M hconn hdisj hedge
  · intro hw
    exact pathwidth_D_short_lower r q hr hq 0
      (pathwidth_monotone (SimpleGraph.deleteEdges_le _) hw)
  · rintro ⟨a, b⟩ he hh
    rcases cycle_edge_cases_D ((SimpleGraph.mem_edgeSet _).1 he) with hc | ⟨i, hi⟩
    · exact (hh hc).elim
    · change ¬ PwLE ((circulantD q r).deleteEdges {s(a, b)}) (2 * r - 1)
      rw [hi]
      exact pathwidth_D_short_lower r q hr hq i
  · rintro _ ⟨i, rfl⟩
    exact (pathwidth_D_upper r N hr hN').2.2 i

private theorem model_B_rigid {r q N : ℕ} (hr : 2 ≤ r) (hq : 4 * r^2 < q + 2 * r) (hN : q ≤ N)
    (M : ZMod q ⊕ ZMod q → Set (ZMod N ⊕ ZMod N))
    (hconn : ∀ h, ((splitB N r).induce (M h)).Connected)
    (hdisj : ∀ h h', h ≠ h' → Disjoint (M h) (M h'))
    (hedge : ∀ h h', (splitB q r).Adj h h' → ∃ u ∈ M h, ∃ v ∈ M h', (splitB N r).Adj u v) :
    ∃ lab : ZMod N ⊕ ZMod N → ZMod q ⊕ ZMod q, (∀ v, v ∈ M (lab v)) ∧
      ∀ a b, s(a, b) ∈ cycleEdgesOf (@cycleStepB N r) → lab a ≠ lab b →
        s(lab a, lab b) ∈ cycleEdgesOf (@cycleStepB q r) ∧
        ∀ x y, (splitB N r).Adj x y → s(lab x, lab y) = s(lab a, lab b) → s(x, y) = s(a, b) := by
  have hm : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hq' : 2 * r < q := by nlinarith
  have hN' : 2 * r < N := by omega
  have : NeZero q := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  apply pathwidth_model_rigid (splitB q r) (splitB N r) r (by omega) _ _ ?_ ?_
    (pathwidth_B_local_delete hr hN') ?_ M hconn hdisj hedge
  · intro hw
    exact pathwidth_B_short_lower r q hr hq 0
      (pathwidth_monotone (SimpleGraph.deleteEdges_le _) hw)
  · rintro ⟨a, b⟩ he hh
    rcases cycle_edge_cases_B ((SimpleGraph.mem_edgeSet _).1 he) with hc | ⟨i, hi⟩
    · exact (hh hc).elim
    · change ¬ PwLE ((splitB q r).deleteEdges {s(a, b)}) (2 * r - 1)
      rw [hi]
      exact pathwidth_B_short_lower r q hr hq i
  · rintro _ ⟨i | i, rfl⟩
    · exact pathwidth_B_delete_spoke hr hN' i
    · exact pathwidth_B_delete_long hr hN' i

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Orient the host cycle and count the changes of branch label on an arc.

private theorem cast_ne_zero_of_pos_lt {n k : ℕ} (hk : 0 < k) (hn : k < n) :
    (k : ZMod n) ≠ 0 := by
  intro h
  have e := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hn, ZMod.val_zero] at e
  omega

private theorem cycle_edge_start_unique {n : ℕ} (hn : 2 < n) {x y : ZMod n}
    (h : s(x, x + 1) = s(y, y + 1)) : x = y := by
  rcases Sym2.eq_iff.1 h with hh | ⟨h₁, h₂⟩
  · exact hh.1
  · have he : ((2 : ℕ) : ZMod n) = 0 := by
      push_cast
      linear_combination h₂ - h₁
    exact (cast_ne_zero_of_pos_lt (by omega) hn he).elim

private theorem orientation {n q : ℕ} [NeZero n] (hq : 2 < q) (f : ZMod n → ZMod q)
    (step : ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1 ∨ f x = f (x + 1) + 1)
    (unique : ∀ x y, f (x + 1) ≠ f x → s(f x, f (x + 1)) = s(f y, f (y + 1)) → x = y)
    (ha : ∃ a, f (a + 1) = f a + 1) :
    ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1 := by
  obtain ⟨a, ha⟩ := ha
  have one_ne : (1 : ZMod q) ≠ 0 := by
    simpa using (cast_ne_zero_of_pos_lt (by omega : 0 < 1) (by omega : 1 < q))
  have noDown (x z : ZMod n) (hz : f (z + 1) = f z + 1) (shared : f (z + 1) = f x)
      (down : f x = f (x + 1) + 1) : False := by
    have hn : f (z + 1) ≠ f z := by
      intro e
      exact one_ne (by linear_combination e - hz)
    have hpair : s(f z, f (z + 1)) = s(f x, f (x + 1)) := by
      apply Sym2.eq_iff.2
      exact .inr ⟨by linear_combination shared - hz + down, shared⟩
    have he := unique z x hn hpair
    subst z
    have htwo : ((2 : ℕ) : ZMod q) = 0 := by
      push_cast
      linear_combination -hz - down
    exact cast_ne_zero_of_pos_lt (by omega) hq htwo
  have anchor (k : ℕ) :
      ∃ z, f (z + 1) = f z + 1 ∧ f (z + 1) = f (a + 1 + (k : ZMod n)) := by
    induction k with
    | zero => exact ⟨a, ha, by simp⟩
    | succ k ih =>
      obtain ⟨z, hz, shared⟩ := ih
      let x := a + 1 + (k : ZMod n)
      have hx : a + 1 + ((k + 1 : ℕ) : ZMod n) = x + 1 := by simp [x, Nat.cast_add, add_assoc]
      rw [hx]
      rcases step x with h | h | h
      · exact ⟨z, hz, shared.trans h.symm⟩
      · exact ⟨x, h, rfl⟩
      · exact (noDown x z hz shared h).elim
  intro x
  rcases step x with h | h | h
  · exact .inl h
  · exact .inr h
  · obtain ⟨z, hz, hshared⟩ := anchor (coordinate (a + 1) x)
    rw [coordinate_spec] at hshared
    exact (noDown x z hz hshared h).elim

private def arcCount {n q : ℕ} (f : ZMod n → ZMod q) (u : ZMod n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => arcCount f u k + if f (u + ((k + 1 : ℕ) : ZMod n)) = f (u + (k : ZMod n)) then 0 else 1

private theorem arcCount_mono {n q : ℕ} (f : ZMod n → ZMod q) (u : ZMod n) :
    Monotone (arcCount f u) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [arcCount]
  omega

private theorem arcCount_crosses {n q : ℕ} (f : ZMod n → ZMod q) (u : ZMod n) (j d : ℕ)
    (hd : d < arcCount f u j) :
    ∃ i < j, arcCount f u i = d ∧ arcCount f u (i + 1) = d + 1 := by
  induction j with
  | zero => simp [arcCount] at hd
  | succ j ih =>
    by_cases h : d < arcCount f u j
    · obtain ⟨i, hi, ha, hb⟩ := ih h
      exact ⟨i, by omega, ha, hb⟩
    · rw [arcCount] at hd
      split at hd
      · omega
      · rename_i hc
        have he : arcCount f u j = d := by omega
        exact ⟨j, by omega, he, by rw [arcCount, if_neg hc, he]⟩

private theorem arcCount_label {n q : ℕ} (f : ZMod n → ZMod q) (u : ZMod n)
    (step : ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1) (j : ℕ) :
    f (u + (j : ZMod n)) = f u + (arcCount f u j : ZMod q) := by
  induction j with
  | zero => simp [arcCount]
  | succ j ih =>
    have he : u + ((j + 1 : ℕ) : ZMod n) = u + (j : ZMod n) + 1 := by simp [Nat.cast_add, add_assoc]
    rw [arcCount, he]
    split
    · rename_i h
      simpa only [Nat.add_zero] using h.trans ih
    · rename_i h
      have he' := ((step _).resolve_left h)
      rw [he', ih, Nat.cast_add, Nat.cast_one, add_assoc]

private theorem arcCount_bound {n q : ℕ} [NeZero n] (hn : 2 < n) (hq : 2 < q) (f : ZMod n → ZMod q)
    (u : ZMod n) (step : ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1)
    (unique : ∀ x y, f (x + 1) ≠ f x → s(f x, f (x + 1)) = s(f y, f (y + 1)) → x = y)
    (j : ℕ) (hj : j < n) : arcCount f u j ≤ q := by
  by_contra! h
  obtain ⟨i₀, hi₀, h₀, h₀'⟩ := arcCount_crosses f u j 0 (by omega)
  obtain ⟨i₁, hi₁, h₁, h₁'⟩ := arcCount_crosses f u j q h
  let x := u + (i₀ : ZMod n)
  let y := u + (i₁ : ZMod n)
  have ex : x + 1 = u + ((i₀ + 1 : ℕ) : ZMod n) := by simp [x, Nat.cast_add, add_assoc]
  have ey : y + 1 = u + ((i₁ + 1 : ℕ) : ZMod n) := by simp [y, Nat.cast_add, add_assoc]
  have lx : f x = f u := by simp [x, arcCount_label f u step, h₀]
  have ly : f y = f u := by simp [y, arcCount_label f u step, h₁, ZMod.natCast_self]
  have lxs : f (x + 1) = f u + 1 := by
    rw [ex, arcCount_label f u step, h₀', Nat.zero_add, Nat.cast_one]
  have lys : f (y + 1) = f u + 1 := by
    rw [ey, arcCount_label f u step, h₁', Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]
  have hchg : f (x + 1) ≠ f x := by
    intro hno
    have hh : f (u + ((i₀ + 1 : ℕ) : ZMod n)) = f (u + (i₀ : ZMod n)) := by
      simpa only [← ex] using hno
    rw [arcCount, if_pos hh] at h₀'
    omega
  have he := unique x y hchg (by rw [lx, ly, lxs, lys])
  have hh := congrArg (coordinate u) he
  have hx : coordinate u x = i₀ := by
    simp only [x, coordinate, add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega : i₀ < n)]
  have hy : coordinate u y = i₁ := by
    simp only [y, coordinate, add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega : i₁ < n)]
  rw [hx, hy] at hh
  have heq : arcCount f u i₀ = arcCount f u i₁ := congrArg _ hh
  omega

private def arcSet {n q : ℕ} [NeZero n] (f : ZMod n → ZMod q) (a : ZMod q) (δ : ℕ) :
    Finset (ZMod n) := Finset.univ.filter fun x => ∃ j ≤ δ, f x = a + (j : ZMod q)

private theorem forward_arc {n q : ℕ} [NeZero n] [NeZero q] (hn : 2 < n) (hq : 2 < q)
    (f : ZMod n → ZMod q)
    (step : ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1)
    (unique : ∀ x y, f (x + 1) ≠ f x → s(f x, f (x + 1)) = s(f y, f (y + 1)) → x = y)
    (a : ZMod q) (δ κ : ℕ) (hδ : 0 < δ) (hδq : δ < q)
    (u v : ZMod n) (hu : f u = a) (hv : f v = a + (δ : ZMod q))
    (dist : ∀ k : ℕ, (v = u + (k : ZMod n) ∨ u = v + (k : ZMod n)) → κ ≤ k) :
    κ + 1 ≤ (arcSet f a δ).card := by
  classical
  let j := coordinate u v
  have hval := coordinate_spec u v
  have hj := coordinate_lt u v
  have hd := arcCount_bound hn hq f u step unique j hj
  have he : (arcCount f u j : ZMod q) = (δ : ZMod q) := by
    apply add_left_cancel (a := a)
    rw [← hu, ← arcCount_label f u step j, hval, hv, hu]
  have hlt : arcCount f u j < q := by
    by_contra! hh
    have e : arcCount f u j = q := by omega
    rw [e, ZMod.natCast_self] at he
    exact cast_ne_zero_of_pos_lt hδ hδq he.symm
  have heq := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hδq] at heq
  have hk := dist j (.inl hval.symm)
  have hcard : (Finset.range (j + 1)).card ≤ (arcSet f a δ).card := by
    apply Finset.card_le_card_of_injOn (fun t : ℕ => u + (t : ZMod n))
    · intro t ht
      have htl : t ≤ j := by have := Finset.mem_range.1 ht; omega
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_univ _, arcCount f u t,
        (arcCount_mono f u htl).trans (le_of_eq heq), by rw [arcCount_label f u step, hu]⟩
    · intro t ht s hs e
      have ht' : t < n := by have := Finset.mem_range.1 ht; omega
      have hs' : s < n := by have := Finset.mem_range.1 hs; omega
      have e' : (t : ZMod n) = (s : ZMod n) := add_left_cancel e
      have hh := congrArg ZMod.val e'
      simpa only [ZMod.val_natCast_of_lt ht', ZMod.val_natCast_of_lt hs'] using hh
  rw [Finset.card_range] at hcard
  omega

private theorem cyclic_arc_lower {n q : ℕ} [NeZero n] [NeZero q] (hn : 2 < n) (hq : 2 < q)
    (f : ZMod n → ZMod q)
    (step : ∀ x, f (x + 1) = f x ∨ f (x + 1) = f x + 1 ∨ f x = f (x + 1) + 1)
    (unique : ∀ x y, f (x + 1) ≠ f x → s(f x, f (x + 1)) = s(f y, f (y + 1)) → x = y)
    (a : ZMod q) (δ κ : ℕ) (hδ : 0 < δ) (hδq : δ < q)
    (u v : ZMod n) (hu : f u = a) (hv : f v = a + (δ : ZMod q))
    (dist : ∀ k : ℕ, (v = u + (k : ZMod n) ∨ u = v + (k : ZMod n)) → κ ≤ k) :
    κ + 1 ≤ (arcSet f a δ).card := by
  classical
  by_cases h : ∃ x, f (x + 1) = f x + 1
  · exact forward_arc hn hq f (orientation hq f step unique h) unique a δ κ hδ hδq u v hu hv dist
  · let g (x : ZMod n) := f (-x)
    have gs (x : ZMod n) : g (x + 1) = g x ∨ g (x + 1) = g x + 1 := by
      let y := -(x + 1)
      have he : y + 1 = -x := by dsimp [y]; abel
      rcases step y with h₁ | h₂ | h₃
      · exact .inl ((congrArg f he).symm.trans h₁ |>.symm)
      · exact (h ⟨y, h₂⟩).elim
      · exact .inr (h₃.trans (congrArg (fun z => f z + 1) he))
    have gu (x y : ZMod n) (hne : g (x + 1) ≠ g x)
        (he : s(g x, g (x + 1)) = s(g y, g (y + 1))) : x = y := by
      have ex : -(x + 1) + 1 = -x := by abel
      have ey : -(y + 1) + 1 = -y := by abel
      have hh := unique (-(x + 1)) (-(y + 1)) (by rw [ex]; exact Ne.symm hne) (by
        rw [ex, ey]
        exact (Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)).trans
          (he.trans (Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩))))
      exact add_right_cancel (neg_injective hh)
    have hdist (k : ℕ) (hK : -v = -u + (k : ZMod n) ∨ -u = -v + (k : ZMod n)) : κ ≤ k := by
      apply dist
      rcases hK with he | he
      · exact .inr (by linear_combination he)
      · exact .inl (by linear_combination he)
    have hp := forward_arc hn hq g gs gu a δ κ hδ hδq (-u) (-v)
      (by simpa [g] using hu) (by simpa [g] using hv) hdist
    apply hp.trans
    apply Finset.card_le_card_of_injOn (fun x : ZMod n => -x) _ neg_injective.injOn
    intro x hx
    simpa only [Finset.mem_coe, arcSet, Finset.mem_filter, Finset.mem_univ, true_and, g] using hx

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Average the resulting arc-size inequalities over starting positions or alternating pairs.

private def cycleLabel {V W : Type} {n q : ℕ}
    (eH : W ≃ ZMod q) (eG : V ≃ ZMod n) (label : V → W) (x : ZMod n) : ZMod q :=
  eH (label (eG.symm x))

private theorem cycle_edge_coords {V : Type} {n : ℕ} (e : V ≃ ZMod n) (next : V → V)
    (hs : ∀ x, e (next x) = e x + 1) (x y : V) :
    s(x, y) ∈ cycleEdgesOf next ↔ e y = e x + 1 ∨ e x = e y + 1 := by
  constructor
  · rintro ⟨z, hz⟩
    rcases Sym2.eq_iff.1 hz with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact .inl ((congrArg e h).symm.trans (hs _))
    · exact .inr ((congrArg e h).symm.trans (hs _))
  · rintro (h | h)
    · exact ⟨x, congrArg (fun z => s(x, z)) (e.injective ((hs x).trans h.symm))⟩
    · exact ⟨y, (congrArg (fun z => s(y, z)) (e.injective ((hs y).trans h.symm))).trans
        (swap_edge_eq _ _)⟩

private def RespectsModelCycle {V W : Type} (G : SimpleGraph V) (nextH : W → W) (nextG : V → V)
    (lab : V → W) : Prop :=
  ∀ x y, s(x, y) ∈ cycleEdgesOf nextG → lab x ≠ lab y →
    s(lab x, lab y) ∈ cycleEdgesOf nextH ∧
    ∀ u v, G.Adj u v → s(lab u, lab v) = s(lab x, lab y) → s(u, v) = s(x, y)

private theorem model_arc_lower {V W : Type} {n q : ℕ} [NeZero n] [NeZero q]
    (hn : 2 < n) (hq : 2 < q)
    (H : SimpleGraph W) (G : SimpleGraph V) (nextH : W → W) (nextG : V → V)
    (eH : W ≃ ZMod q) (eG : V ≃ ZMod n)
    (stepH : ∀ x, eH (nextH x) = eH x + 1) (stepG : ∀ x, eG (nextG x) = eG x + 1)
    (adjG : ∀ x, G.Adj x (nextG x))
    (M : W → Set V) (disj : ∀ x y, x ≠ y → Disjoint (M x) (M y))
    (witness : ∀ x y, H.Adj x y → ∃ u ∈ M x, ∃ v ∈ M y, G.Adj u v)
    (lab : V → W) (hlab : ∀ x, x ∈ M (lab x))
    (rigid : RespectsModelCycle G nextH nextG lab)
    (a : ZMod q) (δ κ : ℕ) (hδ : 0 < δ) (hδq : δ < q)
    (hshort : H.Adj (eH.symm a) (eH.symm (a + (δ : ZMod q))))
    (hoff : s(eH.symm a, eH.symm (a + (δ : ZMod q))) ∉ cycleEdgesOf nextH)
    (hostDist : ∀ u v, G.Adj u v → s(u, v) ∉ cycleEdgesOf nextG →
      ∀ k : ℕ, (eG v = eG u + (k : ZMod n) ∨ eG u = eG v + (k : ZMod n)) → κ ≤ k) :
    κ + 1 ≤ (arcSet (cycleLabel eH eG lab) a δ).card := by
  classical
  let f := cycleLabel eH eG lab
  have same {x : V} {h : W} (hx : x ∈ M h) : lab x = h := by
    by_contra! h
    exact Set.disjoint_left.1 (disj _ _ h) (hlab x) hx
  have enext (x : ZMod n) : nextG (eG.symm x) = eG.symm (x + 1) := by
    apply eG.injective
    simp [stepG]
  have ec (x : ZMod n) : s(eG.symm x, eG.symm (x + 1)) ∈ cycleEdgesOf nextG :=
    ⟨eG.symm x, congrArg _ (enext x)⟩
  have ea (x : ZMod n) : G.Adj (eG.symm x) (eG.symm (x + 1)) := by
    rw [← enext]
    exact adjG _
  have hstep (x : ZMod n) : f (x + 1) = f x ∨ f (x + 1) = f x + 1 ∨ f x = f (x + 1) + 1 := by
    by_cases eq : lab (eG.symm x) = lab (eG.symm (x + 1))
    · exact .inl ((congrArg eH eq).symm)
    · exact .inr ((cycle_edge_coords eH nextH stepH _ _).1
        ((rigid _ _ (ec x) eq).1))
  have hunique (x y : ZMod n) (h : f (x + 1) ≠ f x)
      (heq : s(f x, f (x + 1)) = s(f y, f (y + 1))) : x = y := by
    have h₁ : lab (eG.symm x) ≠ lab (eG.symm (x + 1)) := by
      intro he
      exact h ((congrArg eH he).symm)
    have heq' : s(lab (eG.symm y), lab (eG.symm (y + 1))) =
        s(lab (eG.symm x), lab (eG.symm (x + 1))) := by
      apply Sym2.eq_iff.2
      rcases Sym2.eq_iff.1 heq.symm with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
      · exact .inl ⟨eH.injective h₂, eH.injective h₃⟩
      · exact .inr ⟨eH.injective h₂, eH.injective h₃⟩
    have h₃ := (rigid _ _ (ec x) h₁).2 _ _ (ea y) heq'
    apply cycle_edge_start_unique hn
    apply Sym2.eq_iff.2
    rcases Sym2.eq_iff.1 h₃.symm with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
    · exact .inl ⟨eG.symm.injective h₂, eG.symm.injective h₃⟩
    · exact .inr ⟨eG.symm.injective h₂, eG.symm.injective h₃⟩
  obtain ⟨u₀, hu₀, v₀, hv₀, edge⟩ := witness _ _ hshort
  have hul := same hu₀
  have hvl := same hv₀
  have hnedge : s(u₀, v₀) ∉ cycleEdgesOf nextG := by
    intro h
    have hne : lab u₀ ≠ lab v₀ := fun he => hshort.ne (hul.symm.trans he |>.trans hvl)
    apply hoff
    simpa only [hul, hvl] using (rigid u₀ v₀ h hne).1
  exact cyclic_arc_lower hn hq f hstep hunique a δ κ hδ hδq (eG u₀) (eG v₀)
    (by simp [f, cycleLabel, hul]) (by simp [f, cycleLabel, hvl]) (hostDist u₀ v₀ edge hnedge)

private def fiberWeight {n q : ℕ} [NeZero n] (f : ZMod n → ZMod q) (a : ZMod q) : ℕ :=
  (Finset.univ.filter fun x => f x = a).card

private theorem sum_fiberWeight {n q : ℕ} [NeZero n] [NeZero q] (f : ZMod n → ZMod q) :
    ∑ a : ZMod q, fiberWeight f a = n := by
  classical
  unfold fiberWeight
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

private theorem arc_card_le_sum {n q : ℕ} [NeZero n] (f : ZMod n → ZMod q) (a : ZMod q)
    (δ : ℕ) : (arcSet f a δ).card ≤ ∑ i ∈ Finset.range (δ + 1), fiberWeight f (a + (i : ZMod q)) := by
  classical
  unfold arcSet fiberWeight
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  split
  · rename_i hp
    obtain ⟨i, hi, hfi⟩ := hp
    have hmem : i ∈ Finset.range (δ + 1) := Finset.mem_range.2 (by omega)
    simpa only [hfi, if_true] using
      (Finset.single_le_sum (f := fun j : ℕ => if f x = a + (j : ZMod q) then 1 else 0)
         (fun _ _ => Nat.zero_le _) hmem)
  · exact Nat.zero_le _

private theorem step_average_all {n q : ℕ} [NeZero n] [NeZero q] (f : ZMod n → ZMod q) (δ κ : ℕ)
    (ha : ∀ a, κ + 1 ≤ (arcSet f a δ).card) :
    (κ + 1) * q ≤ (δ + 1) * n := by
  classical
  calc
    (κ + 1) * q = ∑ _a : ZMod q, (κ + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ a : ZMod q, ∑ i ∈ Finset.range (δ + 1), fiberWeight f (a + (i : ZMod q)) :=
      Finset.sum_le_sum fun a _ => (ha a).trans (arc_card_le_sum f a δ)
    _ = (δ + 1) * n := by
      rw [Finset.sum_comm]
      have sum_shift (i : ℕ) : (∑ a : ZMod q, fiberWeight f (a + (i : ZMod q))) = n := by
        classical
        calc
          _ = ∑ a : ZMod q, fiberWeight f a := Fintype.sum_equiv (Equiv.addRight (i : ZMod q)) _ _ (fun _ => rfl)
          _ = n := sum_fiberWeight f
      simp only [sum_shift, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]

private theorem sum_by_pairs (f : ℕ → ℕ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), f j = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

private theorem step_average_pairs {I : Type} [Fintype I] {n q : ℕ} [NeZero n] [NeZero q]
    (f : ZMod n → ZMod q) (start : I → ZMod q) (K κ : ℕ)
    (ha : ∀ a, κ + 1 ≤ (arcSet f (start a) (2 * K + 1)).card)
    (pair : ∀ t : ZMod q,
      (∑ a : I, (fiberWeight f (start a + t) + fiberWeight f (start a + t + 1))) = n) :
    (κ + 1) * Fintype.card I ≤ (K + 1) * n := by
  classical
  calc
    (κ + 1) * Fintype.card I = ∑ _a : I, (κ + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ a : I, ∑ j ∈ Finset.range (2 * K + 1 + 1), fiberWeight f (start a + (j : ZMod q)) :=
      Finset.sum_le_sum fun a _ => (ha a).trans (arc_card_le_sum f (start a) _)
    _ = (K + 1) * n := by
      have he : 2 * K + 1 + 1 = 2 * (K + 1) := by omega
      simp only [he, sum_by_pairs, Nat.cast_add, Nat.cast_one, ← add_assoc]
      rw [Finset.sum_comm]
      simp only [pair, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Use modular inverses for cycle coordinates and compute the two possible short-edge offsets.

private theorem inverse_mul {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) :
    (aInv n r : ZMod n) * (r : ZMod n) = 1 := by
  unfold aInv
  rw [ZMod.natCast_zmod_val, mul_comm]
  exact ZMod.coe_mul_inv_eq_one r h.symm

private theorem inverse_interior {n r : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (h : Nat.Coprime n r) : 1 < aInv n r ∧ aInv n r + 1 < n := by
  have prod := inverse_mul h
  have hval : aInv n r < n := ZMod.val_lt _
  have hN : (1 : ZMod n) ≠ 0 := by
    simpa using (cast_ne_zero_of_pos_lt (by omega : 0 < 1) (by omega : 1 < n))
  have a0 : aInv n r ≠ 0 := by
    intro he
    rw [he, Nat.cast_zero, zero_mul] at prod
    exact hN prod.symm
  have a1 : aInv n r ≠ 1 := by
    intro he
    rw [he, Nat.cast_one, one_mul] at prod
    have e := congrArg ZMod.val prod
    rw [← Nat.cast_one (R := ZMod n), ZMod.val_natCast_of_lt (by omega : r < n),
      ZMod.val_natCast_of_lt (by omega : 1 < n)] at e
    omega
  have alast : aInv n r ≠ n - 1 := by
    intro he
    have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [he, hn1, neg_one_mul] at prod
    have e : (r : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
      rw [hn1]
      linear_combination -prod
    have e' := congrArg ZMod.val e
    rw [ZMod.val_natCast_of_lt (by omega : r < n),
      ZMod.val_natCast_of_lt (by omega : n - 1 < n)] at e'
    omega
  omega

private def scale {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) : ZMod n ≃ ZMod n where
  toFun x := (aInv n r : ZMod n) * x
  invFun x := (r : ZMod n) * x
  left_inv x := by
    change (r : ZMod n) * ((aInv n r : ZMod n) * x) = x
    rw [← mul_assoc, mul_comm (r : ZMod n), inverse_mul h, one_mul]
  right_inv x := by
    change (aInv n r : ZMod n) * ((r : ZMod n) * x) = x
    rw [← mul_assoc, inverse_mul h, one_mul]

private theorem scale_add_long {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) (x : ZMod n) :
    scale h (x + (r : ZMod n)) = scale h x + 1 := by
  change (aInv n r : ZMod n) * (x + (r : ZMod n)) = (aInv n r : ZMod n) * x + 1
  rw [mul_add, inverse_mul h]

private theorem scale_short {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) (x : ZMod n) :
    scale h (x + 1) = scale h x + (aInv n r : ZMod n) := by
  change (aInv n r : ZMod n) * (x + 1) = (aInv n r : ZMod n) * x + (aInv n r : ZMod n)
  rw [mul_add, mul_one]

private def doubleInput (n : ℕ) : ℤ →+ ZMod (2 * n) where
  toFun x := (2 : ZMod (2 * n)) * (x : ZMod (2 * n))
  map_zero' := by simp
  map_add' x y := by push_cast; ring

private def widen (n : ℕ) : ZMod n →+ ZMod (2 * n) :=
  ZMod.lift n ⟨doubleInput n, by
    change (2 : ZMod (2 * n)) * ((n : ℤ) : ZMod (2 * n)) = 0
    rw [Int.cast_natCast]
    change ((2 : ℕ) : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0
    rw [← Nat.cast_mul, ZMod.natCast_self]⟩

private theorem widen_nat (n k : ℕ) : widen n (k : ZMod n) = ((2 * k : ℕ) : ZMod (2 * n)) := by
  calc
    widen n (k : ZMod n) = widen n ((k : ℤ) : ZMod n) := by simp
    _ = ((2 * k : ℕ) : ZMod (2 * n)) := by
      rw [widen, ZMod.lift_coe]
      simp [doubleInput, Nat.cast_mul]

private theorem widen_add_one (n : ℕ) (x : ZMod n) :
    widen n (x + 1) = widen n x + 2 := by
  rw [map_add, ← Nat.cast_one (R := ZMod n), widen_nat]
  simp

private def parityCode {n : ℕ} : ZMod n ⊕ ZMod n → ZMod (2 * n)
  | .inl x => widen n x
  | .inr x => widen n x + 1

private theorem parityCode_val {n : ℕ} [NeZero n] (x : ZMod n) :
    (parityCode (Sum.inl x)).val = 2 * x.val ∧ (parityCode (Sum.inr x)).val = 2 * x.val + 1 := by
  have hx := ZMod.val_lt x
  have he : widen n x = ((2 * x.val : ℕ) : ZMod (2 * n)) := by
    rw [← widen_nat, ZMod.natCast_zmod_val]
  constructor
  · change (widen n x).val = _
    rw [he, ZMod.val_natCast_of_lt (by omega)]
  · change (widen n x + 1).val = _
    rw [he, ← Nat.cast_one (R := ZMod (2 * n)), ← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]

private noncomputable def parityEquiv (n : ℕ) [NeZero n] : (ZMod n ⊕ ZMod n) ≃ ZMod (2 * n) := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  have : NeZero (2 * n) := ⟨by omega⟩
  apply Equiv.ofBijective parityCode
  constructor
  · intro x y he
    have hf := congrArg ZMod.val he
    cases x <;> cases y
    · rename_i x y
      rw [(parityCode_val x).1, (parityCode_val y).1] at hf
      exact congrArg Sum.inl (ZMod.val_injective n (by omega))
    · rename_i x y
      rw [(parityCode_val x).1, (parityCode_val y).2] at hf
      omega
    · rename_i x y
      rw [(parityCode_val x).2, (parityCode_val y).1] at hf
      omega
    · rename_i x y
      rw [(parityCode_val x).2, (parityCode_val y).2] at hf
      exact congrArg Sum.inr (ZMod.val_injective n (by omega))
  · intro z
    have hz := ZMod.val_lt z
    let x : ZMod n := ((z.val / 2 : ℕ) : ZMod n)
    have hx : x.val = z.val / 2 := ZMod.val_natCast_of_lt (by omega)
    by_cases he : z.val % 2 = 0
    · exact ⟨Sum.inl x, ZMod.val_injective _ (by rw [(parityCode_val x).1, hx]; omega)⟩
    · exact ⟨Sum.inr x, ZMod.val_injective _ (by rw [(parityCode_val x).2, hx]; omega)⟩

private theorem parityEquiv_left {n : ℕ} [NeZero n] (x : ZMod n) :
    parityEquiv n (Sum.inl x) = widen n x := rfl

private theorem parityEquiv_right {n : ℕ} [NeZero n] (x : ZMod n) :
    parityEquiv n (Sum.inr x) = widen n x + 1 := rfl

private noncomputable def scaleB {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) : (ZMod n ⊕ ZMod n) ≃ ZMod (2 * n) :=
  (Equiv.sumCongr (scale h) (scale h)).trans (parityEquiv n)

private theorem scaleB_inl {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) (x : ZMod n) :
    scaleB h (Sum.inl x) = widen n (scale h x) := rfl

private theorem scaleB_inr {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) (x : ZMod n) :
    scaleB h (Sum.inr x) = widen n (scale h x) + 1 := rfl

private theorem scaleB_cycle_step {n r : ℕ} [NeZero n] (h : Nat.Coprime n r)
    (x : ZMod n ⊕ ZMod n) : scaleB h (cycleStepB r x) = scaleB h x + 1 := by
  rcases x with j | j
  · rfl
  · change widen n (scale h (j + (r : ZMod n))) = widen n (scale h j) + 1 + 1
    rw [scale_add_long, widen_add_one]
    ring

private theorem scaleB_short {n r : ℕ} [NeZero n] (h : Nat.Coprime n r) (ha : 0 < aInv n r)
    (x : ZMod n) :
    scaleB h (Sum.inl (x + 1)) = scaleB h (Sum.inr x) + ((2 * aInv n r - 1 : ℕ) : ZMod (2 * n)) := by
  rw [scaleB_inl, scaleB_inr, scale_short, map_add, widen_nat, add_assoc]
  congr 1
  rw [← Nat.cast_one (R := ZMod (2 * n)), ← Nat.cast_add, Nat.add_comm,
    Nat.sub_add_cancel (by omega : 1 ≤ 2 * aInv n r)]

private theorem circulant_forward_edge {n r k : ℕ} (hn : 2 * r < n) (hr : 2 ≤ r)
    (x : ZMod n) (hk : k = 1 ∨ k = r) : (circulantD n r).Adj x (x + (k : ZMod n)) :=
  d_step hr hn x hk

private theorem splitB_forward_edge {n r : ℕ} (x : ZMod n ⊕ ZMod n) :
    (splitB n r).Adj x (cycleStepB r x) := by
  rcases x with x | x
  · exact ((splitB_step_iff _ _).2 ⟨0, .inl rfl, by simp⟩).symm
  · exact (splitB_step_iff _ _).2 ⟨r, .inr (.inr rfl), rfl⟩

private theorem cast_complement {n k : ℕ} (hk : k ≤ n) :
    ((n - k : ℕ) : ZMod n) = -(k : ZMod n) := by
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub]

private theorem short_offset_off_cycle {V : Type} {n j : ℕ} (e : V ≃ ZMod n) (next : V → V)
    (hnx : ∀ x, e (next x) = e x + 1) (hj : 1 < j) (hjn : j + 1 < n)
    (x y : V) (he : e y = e x + (j : ZMod n)) :
    s(x, y) ∉ cycleEdgesOf next := by
  intro hc
  rcases (cycle_edge_coords e next hnx x y).1 hc with f | f
  · have eq : (j : ZMod n) = ((1 : ℕ) : ZMod n) := by
      push_cast
      linear_combination f - he
    have hl := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (by omega : j < n),
      ZMod.val_natCast_of_lt (by omega : 1 < n)] at hl
    omega
  · have eq : (j : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
      rw [cast_complement (by omega : 1 ≤ n), Nat.cast_one]
      linear_combination -f - he
    have hl := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (by omega : j < n), ZMod.val_natCast_of_lt (by omega : n - 1 < n)] at hl
    omega

private theorem short_offset_bound {V : Type} {n j : ℕ} (e : V ≃ ZMod n)
    (hj : 0 < j) (hjn : j < n) (x y x₀ y₀ : V)
    (hpair : s(x, y) = s(x₀, y₀)) (hjump : e y₀ = e x₀ + (j : ZMod n))
    (k : ℕ) (hk : e y = e x + (k : ZMod n) ∨ e x = e y + (k : ZMod n)) :
    min j (n - j) ≤ k := by
  have hcast : (k : ZMod n) = (j : ZMod n) ∨ (k : ZMod n) = -(j : ZMod n) := by
    rcases Sym2.eq_iff.1 hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hk with e' | e'
    · exact .inl (by linear_combination hjump - e')
    · exact .inr (by linear_combination -hjump - e')
    · exact .inr (by linear_combination -hjump - e')
    · exact .inl (by linear_combination hjump - e')
  rcases hcast with hit | hit
  · have hm := congrArg ZMod.val hit
    rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hjn] at hm
    exact (min_le_left _ _).trans (hm ▸ Nat.mod_le _ _)
  · rw [← cast_complement (by omega : j ≤ n)] at hit
    have hm := congrArg ZMod.val hit
    rw [ZMod.val_natCast, ZMod.val_natCast_of_lt (by omega : n - j < n)] at hm
    exact (min_le_right _ _).trans (hm ▸ Nat.mod_le _ _)

private theorem host_distance_D {n r : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (h : Nat.Coprime n r) (x y : ZMod n) (he : (circulantD n r).Adj x y)
    (hoff : s(x, y) ∉ cycleEdgesOf (fun z : ZMod n => z + (r : ZMod n)))
    (k : ℕ) (hk : scale h y = scale h x + (k : ZMod n) ∨ scale h x = scale h y + (k : ZMod n)) :
    dR n r ≤ k := by
  rcases cycle_edge_cases_D he with he | ⟨i, hi⟩
  · exact (hoff he).elim
  · obtain ⟨ha, hal⟩ := inverse_interior hr hn h
    exact short_offset_bound (scale h) (by omega) (by omega) x y i (i + 1) hi (scale_short h i) k hk

private theorem host_distance_B {n r : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (h : Nat.Coprime n r) (x y : ZMod n ⊕ ZMod n) (he : (splitB n r).Adj x y)
    (hoff : s(x, y) ∉ cycleEdgesOf (@cycleStepB n r))
    (k : ℕ) (hk : scaleB h y = scaleB h x + (k : ZMod (2 * n)) ∨
      scaleB h x = scaleB h y + (k : ZMod (2 * n))) :
    bR n r ≤ k := by
  rcases cycle_edge_cases_B he with he | ⟨i, hi⟩
  · exact (hoff he).elim
  · obtain ⟨ha, hal⟩ := inverse_interior hr hn h
    have hdist := short_offset_bound (scaleB h) (by omega : 0 < 2 * aInv n r - 1)
      (by omega : 2 * aInv n r - 1 < 2 * n) x y (Sum.inr i) (Sum.inl (i + 1))
      hi (scaleB_short h (by omega) i) k hk
    convert hdist using 2 <;> unfold bR <;> omega

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Derive the necessary distance inequalities for both minor models.

private theorem D_bounds {n r : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (h : Nat.Coprime n r) : 1 < dR n r ∧ dR n r + 1 < n := by
  obtain ⟨ha, ha'⟩ := inverse_interior hr hn h
  unfold dR
  constructor
  · exact lt_min (by omega) (by omega)
  · have := min_le_left (aInv n r) (n - aInv n r)
    omega

private theorem D_base_short {q r : ℕ} [NeZero q] (hr : 2 ≤ r) (hq : 2 * r < q)
    (h : Nat.Coprime q r) (a : ZMod q) :
    (circulantD q r).Adj ((scale h).symm a) ((scale h).symm (a + (dR q r : ZMod q))) := by
  let x := (scale h).symm a
  have hx : scale h x = a := (scale h).apply_symm_apply a
  obtain ⟨hinv, hlim⟩ := inverse_interior hr hq h
  unfold dR
  by_cases hc : aInv q r ≤ q - aInv q r
  · rw [min_eq_left hc]
    have he : (scale h).symm (a + (aInv q r : ZMod q)) = x + 1 := by
      apply (scale h).injective
      rw [Equiv.apply_symm_apply, scale_short, hx]
    rw [he]
    simpa only [Nat.cast_one] using circulant_forward_edge hq hr x (k := 1) (.inl rfl)
  · rw [min_eq_right (by omega)]
    have he : (scale h).symm (a + ((q - aInv q r : ℕ) : ZMod q)) = x - 1 := by
      apply (scale h).injective
      rw [Equiv.apply_symm_apply, cast_complement (by omega)]
      have hshort := scale_short h (x - 1)
      rw [sub_add_cancel, hx] at hshort
      linear_combination hshort
    rw [he]
    have hs := (circulant_forward_edge hq hr (x - 1) (k := 1) (.inl rfl)).symm
    simpa only [Nat.cast_one, sub_add_cancel] using hs

private theorem distance_D (r q N : ℕ) (hr : 2 ≤ r) (hq : 4 * r^2 < q + 2 * r) (hN : q ≤ N)
    (hqr : Nat.Coprime q r) (hNr : Nat.Coprime N r)
    (hm : HadwigerConj.IsMinor (circulantD q r) (circulantD N r)) :
    (dR N r + 1) * q ≤ (dR q r + 1) * N := by
  have hmul : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hq' : 2 * r < q := by nlinarith
  have hN' : 2 * r < N := by omega
  have : NeZero q := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  obtain ⟨M, conn, disj, witness⟩ := hm
  obtain ⟨lab, hl, rigid⟩ := model_D_rigid hr hq hN M conn disj witness
  obtain ⟨hd, hdl⟩ := D_bounds hr hq' hqr
  apply step_average_all (cycleLabel (scale hqr) (scale hNr) lab) (dR q r) (dR N r)
  intro a
  apply model_arc_lower (by omega : 2 < N) (by omega : 2 < q)
    (circulantD q r) (circulantD N r) (fun x => x + (r : ZMod q)) (fun x => x + (r : ZMod N))
    (scale hqr) (scale hNr) (scale_add_long hqr) (scale_add_long hNr)
    (fun x => circulant_forward_edge hN' hr x (.inr rfl))
    M disj witness lab hl rigid a (dR q r) (dR N r) (by omega) (by omega)
    (D_base_short hr hq' hqr a) _ (host_distance_D hr hN' hNr)
  apply short_offset_off_cycle (scale hqr) _ (scale_add_long hqr) hd hdl
  simp

private def B_start (q : ℕ) (b : Bool) (x : ZMod q) : ZMod (2 * q) :=
  widen q x + if b then 1 else 0

private theorem B_bounds {n r : ℕ} [NeZero n] (hr : 2 ≤ r) (hn : 2 * r < n)
    (h : Nat.Coprime n r) :
    1 < bR n r ∧ bR n r + 1 < 2 * n ∧ ∃ K : ℕ, bR n r = 2 * K + 1 := by
  obtain ⟨ha, ha'⟩ := inverse_interior hr hn h
  set J := 2 * aInv n r - 1 with hJ
  have hcomp : 2 * n - 2 * aInv n r + 1 = 2 * n - J := by omega
  have heq : bR n r = min J (2 * n - J) := by
    unfold bR
    rw [hcomp, hJ]
  rw [heq]
  by_cases hh : J ≤ 2 * n - J
  · rw [min_eq_left hh]
    exact ⟨by omega, by omega, aInv n r - 1, by omega⟩
  · rw [min_eq_right (by omega)]
    exact ⟨by omega, by omega, n - aInv n r, by omega⟩

private theorem B_base_shorts {q r : ℕ} [NeZero q] (hr : 2 ≤ r) (hq : 2 * r < q)
    (h : Nat.Coprime q r) :
    ∃ b : Bool, ∀ a : ZMod q,
      (splitB q r).Adj ((scaleB h).symm (B_start q b a))
        ((scaleB h).symm (B_start q b a + (bR q r : ZMod (2 * q)))) := by
  obtain ⟨ha, ha'⟩ := inverse_interior hr hq h
  set J := 2 * aInv q r - 1 with hJ
  have hj : 2 * q - 2 * aInv q r + 1 = 2 * q - J := by omega
  have heq : bR q r = min J (2 * q - J) := by
    unfold bR
    rw [hj, hJ]
  by_cases hh : J ≤ 2 * q - J
  · refine ⟨true, ?_⟩
    intro a
    let x := (scale h).symm a
    have he : scale h x = a := (scale h).apply_symm_apply a
    have eu : (scaleB h).symm (B_start q true a) = Sum.inr x := by
      apply (scaleB h).injective
      simp [scaleB_inr, B_start, he]
    have ev : (scaleB h).symm (B_start q true a + (bR q r : ZMod (2 * q))) = Sum.inl (x + 1) := by
      apply (scaleB h).injective
      rw [Equiv.apply_symm_apply, heq, min_eq_left hh, scaleB_short h (by omega), scaleB_inr, he]
      rfl
    rw [eu, ev]
    exact (splitB_step_iff _ _).2 ⟨1, .inr (.inl rfl), by simp⟩
  · refine ⟨false, ?_⟩
    intro a
    let x := (scale h).symm a
    have he : scale h x = a := (scale h).apply_symm_apply a
    have eu : (scaleB h).symm (B_start q false a) = Sum.inl x := by
      apply (scaleB h).injective
      simp [scaleB_inl, B_start, he]
    have ev : (scaleB h).symm (B_start q false a + (bR q r : ZMod (2 * q))) = Sum.inr (x - 1) := by
      apply (scaleB h).injective
      rw [Equiv.apply_symm_apply, heq, min_eq_right (by omega), cast_complement (by omega)]
      have hs := scaleB_short h (by omega) (x - 1)
      rw [sub_add_cancel, scaleB_inl, he, ← hJ] at hs
      simp [B_start]
      linear_combination hs
    rw [eu, ev]
    exact ((splitB_step_iff _ _).2 ⟨1, .inr (.inl rfl), by simp⟩).symm

private theorem B_weights {n q : ℕ} [NeZero n] [NeZero q] [NeZero (2 * q)]
    (f : ZMod n → ZMod (2 * q)) (b : Bool) (t : ZMod (2 * q)) :
    (∑ a : ZMod q, (fiberWeight f (B_start q b a + t) + fiberWeight f (B_start q b a + t + 1))) = n := by
  classical
  let F := fiberWeight f
  have hs : ∑ a : ZMod q ⊕ ZMod q, F (parityEquiv q a + t) = n := by
    calc
      _ = ∑ a : ZMod (2 * q), F a :=
        Fintype.sum_equiv ((parityEquiv q).trans (Equiv.addRight t)) _ _ (fun _ => rfl)
      _ = n := sum_fiberWeight f
  rw [Fintype.sum_sum_type] at hs
  simp only [parityEquiv_left, parityEquiv_right] at hs
  cases b
  · simp only [B_start, Bool.false_eq_true, if_false, add_zero, Finset.sum_add_distrib]
    change (∑ a : ZMod q, F (widen q a + t)) + (∑ a : ZMod q, F (widen q a + t + 1)) = _
    have e : ∀ a : ZMod q, widen q a + t + 1 = widen q a + 1 + t := by intro a; abel
    simpa only [e] using hs
  · simp only [B_start, if_true, Finset.sum_add_distrib]
    change (∑ a : ZMod q, F (widen q a + 1 + t)) +
      (∑ a : ZMod q, F (widen q a + 1 + t + 1)) = _
    have e : (∑ a : ZMod q, F (widen q a + 1 + t + 1)) = ∑ a : ZMod q, F (widen q a + t) := by
      calc
        _ = ∑ a : ZMod q, F (widen q (a + 1) + t) := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 1
          rw [widen_add_one]
          ring
        _ = _ := Fintype.sum_equiv (Equiv.addRight (1 : ZMod q)) _ _ (fun _ => rfl)
    rw [e, add_comm]
    exact hs

private theorem distance_B (r q N : ℕ) (hr : 2 ≤ r) (hq : 4 * r^2 < q + 2 * r) (hN : q ≤ N)
    (hqr : Nat.Coprime q r) (hNr : Nat.Coprime N r)
    (hm : HadwigerConj.IsMinor (splitB q r) (splitB N r)) :
    (bR N r + 1) * q ≤ (bR q r + 1) * N := by
  have hmul : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have hq' : 2 * r < q := by nlinarith
  have hN' : 2 * r < N := by omega
  have : NeZero q := ⟨by omega⟩
  have : NeZero N := ⟨by omega⟩
  have : NeZero (2 * q) := ⟨by omega⟩
  have : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨M, conn, disj, witness⟩ := hm
  obtain ⟨lab, hl, rigid⟩ := model_B_rigid hr hq hN M conn disj witness
  obtain ⟨hd, hdl, K, hK⟩ := B_bounds hr hq' hqr
  obtain ⟨b, hshort⟩ := B_base_shorts hr hq' hqr
  let f := cycleLabel (scaleB hqr) (scaleB hNr) lab
  have arcs (a : ZMod q) : bR N r + 1 ≤ (arcSet f (B_start q b a) (2 * K + 1)).card := by
    rw [← hK]
    apply model_arc_lower (n := 2 * N) (q := 2 * q) (by omega) (by omega)
      (splitB q r) (splitB N r) (cycleStepB r) (cycleStepB r) (scaleB hqr) (scaleB hNr)
      (scaleB_cycle_step hqr) (scaleB_cycle_step hNr) splitB_forward_edge
      M disj witness lab hl rigid _ (bR q r) (bR N r) (by omega) (by omega)
      (hshort a) _ (host_distance_B hr hN' hNr)
    apply short_offset_off_cycle (scaleB hqr) _ (scaleB_cycle_step hqr) hd hdl
    simp
  have h := step_average_pairs f (B_start q b) K (bR N r) arcs (B_weights f b)
  have hs : (bR q r + 1) * N = (K + 1) * (2 * N) := by rw [hK]; ring
  rw [hs]
  simpa using h

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Use the degree bound to separate routed paths and build a minor model from a weak immersion.

private theorem incident_first {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hne : u ≠ v) : ∃ x, G.Adj u x ∧ s(u, x) ∈ p.edges := by
  cases p with
  | nil => exact (hne rfl).elim
  | @cons a b c edge rest => exact ⟨b, edge, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self⟩

private theorem incident_internal {V : Type} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) (hwu : w ≠ u) (hwv : w ≠ v) :
    ∃ a b, a ≠ b ∧ G.Adj w a ∧ G.Adj w b ∧ s(w, a) ∈ p.edges ∧ s(w, b) ∈ p.edges := by
  induction p with
  | nil => exact (hwu (by simpa using hw)).elim
  | @cons x y z e p ih =>
    have hm : w ∈ p.support := by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
      exact hw.resolve_left hwu
    by_cases hwy : w = y
    · subst w
      cases p with
      | nil => exact (hwv rfl).elim
      | @cons a b c f q =>
        have hn := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hn
        have hne : x ≠ b := by
          intro he
          apply hn.notMem
          rw [SimpleGraph.Walk.support_cons, he]
          exact List.mem_cons_of_mem _ q.start_mem_support
        refine ⟨x, b, hne, e.symm, f, ?_, ?_⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons.2 (.inl (swap_edge_eq _ _))
        · rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ List.mem_cons_self
    · obtain ⟨a, b, hne, ha, hb, hea, heb⟩ := ih hp.of_cons hm hwy hwv
      exact ⟨a, b, hne, ha, hb, List.mem_cons_of_mem _ hea, List.mem_cons_of_mem _ heb⟩

private theorem dropped_internal {V : Type} {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hp : p.IsPath) (hne : u ≠ v) (hx : x ∈ p.dropLast.support) :
    x ∈ p.support ∧ x ≠ v := by
  have hn := p.support_dropLast (SimpleGraph.Walk.not_nil_of_ne hne)
  rw [hn] at hx
  have hp' := hp.support_nodup
  rw [← p.dropLast_support_concat] at hp'
  exact ⟨p.dropLast_support_concat ▸ List.mem_append_left _ hx,
    (List.nodup_append.1 hp').2.2 x hx v (by simp)⟩

private theorem distinct_incident {V : Type} (w a b : V) {P Q : List (Sym2 V)}
    (d : P.Disjoint Q) (ha : s(w, a) ∈ P) (hb : s(w, b) ∈ Q) : a ≠ b := by
  intro e
  exact (List.disjoint_left.1 d) ha (e.symm ▸ hb)

private theorem no_four_neighbors {V : Type} [Finite V] (G : SimpleGraph V)
    (w a b c d : V) (cap : (G.neighborSet w).ncard ≤ 3)
    (ea : G.Adj w a) (eb : G.Adj w b) (ec : G.Adj w c) (ed : G.Adj w d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False := by
  classical
  let s : Finset V := {a, b, c, d}
  have ha : a ∉ ({b, c, d} : Finset V) := by simp [hab, hac, had]
  have hb : b ∉ ({c, d} : Finset V) := by simp [hbc, hbd]
  have hc : c ∉ ({d} : Finset V) := by simpa using hcd
  have hcard : s.card = 4 := by simp [s, Finset.card_insert_of_notMem, ha, hb, hc]
  have hsub : (s : Set V) ⊆ G.neighborSet w := by
    intro x hx
    change x ∈ s at hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ea
    · exact eb
    · exact ec
    · exact ed
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hcard] at hc
  omega

private theorem neighbors_of_three {V : Type} [Finite V] (G : SimpleGraph V) (w a b c : V)
    (h : ∀ x, G.Adj w x → x = a ∨ x = b ∨ x = c) : (G.neighborSet w).ncard ≤ 3 := by
  have hsub : G.neighborSet w ⊆ ({a, b, c} : Set V) := fun x hx => h x hx
  calc
    _ ≤ ({a, b, c} : Set V).ncard := Set.ncard_le_ncard hsub
    _ ≤ 3 := by
      have e₁ := Set.ncard_insert_le a ({b, c} : Set V)
      have e₂ := Set.ncard_insert_le b ({c} : Set V)
      rw [Set.ncard_singleton] at e₂
      omega

private theorem splitB_max_three {n r : ℕ} [NeZero n] (w : ZMod n ⊕ ZMod n) :
    ((splitB n r).neighborSet w).ncard ≤ 3 := by
  cases w with
  | inr w =>
    apply neighbors_of_three _ _ (Sum.inl w) (Sum.inl (w + 1)) (Sum.inl (w + (r : ZMod n)))
    intro x hx
    cases x with
    | inr x => exact (splitB_not_inr_inr _ _ hx).elim
    | inl x =>
      obtain ⟨k, hk, e⟩ := (splitB_step_iff _ _).1 hx
      rcases hk with rfl | rfl | rfl
      · exact .inl (congrArg Sum.inl (by simpa using e))
      · exact .inr (.inl (congrArg Sum.inl (by simpa using e)))
      · exact .inr (.inr (congrArg Sum.inl e))
  | inl w =>
    apply neighbors_of_three _ _ (Sum.inr w) (Sum.inr (w - 1)) (Sum.inr (w - (r : ZMod n)))
    intro x hx
    cases x with
    | inl x => exact (splitB_not_inl_inl _ _ hx).elim
    | inr x =>
      obtain ⟨k, hk, e⟩ := (splitB_step_iff _ _).1 hx.symm
      rcases hk with rfl | rfl | rfl
      · exact .inl ((congrArg Sum.inr (by simpa using e)).symm)
      · exact .inr (.inl (congrArg Sum.inr (by push_cast at e; linear_combination -e)))
      · exact .inr (.inr (congrArg Sum.inr (by linear_combination -e)))

private theorem splitB_two_neighbors {n r : ℕ} (hn : 1 < n) (w : ZMod n ⊕ ZMod n) :
    ∃ a b, a ≠ b ∧ (splitB n r).Adj w a ∧ (splitB n r).Adj w b := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using cast_ne_zero_of_pos_lt (by omega : 0 < 1) hn
  cases w with
  | inr w =>
    refine ⟨Sum.inl w, Sum.inl (w + 1), ?_, (splitB_step_iff _ _).2 ⟨0, .inl rfl, by simp⟩,
      (splitB_step_iff _ _).2 ⟨1, .inr (.inl rfl), by simp⟩⟩
    intro h
    have h' := Sum.inl.inj h
    exact h1 (by linear_combination -h')
  | inl w =>
    refine ⟨Sum.inr w, Sum.inr (w - 1), ?_,
      ((splitB_step_iff _ _).2 ⟨0, .inl rfl, by simp⟩).symm,
      ((splitB_step_iff _ _).2 ⟨1, .inr (.inl rfl), by simp⟩).symm⟩
    intro h
    have h' := Sum.inr.inj h
    exact h1 (by linear_combination h')

private theorem splitB_immersion_minor {q N r : ℕ} (hq : 1 < q) (hN : 0 < N)
    (hi : IsImmersion (splitB q r) (splitB N r)) :
    HadwigerConj.IsMinor (splitB q r) (splitB N r) := by
  classical
  have : NeZero N := ⟨by omega⟩
  let W := ZMod q ⊕ ZMod q
  let V := ZMod N ⊕ ZMod N
  let H := splitB q r
  let G := splitB N r
  obtain ⟨ι, P, inj, path, sep⟩ := hi
  have end_ne {x y : W} (he : H.Adj x y) : ι x ≠ ι y := fun e => he.ne (inj e)
  have no_image (x y c : W) (e : H.Adj x y) (hpx : ι c ∈ (P x y e).support)
      (hcx : ι c ≠ ι x) (hcy : ι c ≠ ι y) : False := by
    obtain ⟨a, b, hab, ea, eb, ha, hb⟩ := incident_internal (P x y e) (path x y e) hpx hcx hcy
    obtain ⟨u, v, huv, eu, ev⟩ := splitB_two_neighbors hq c (r := r)
    obtain ⟨d, ed, hd⟩ := incident_first (P c u eu) (end_ne eu)
    obtain ⟨f, ef, hf⟩ := incident_first (P c v ev) (end_ne ev)
    have de (z : W) : s(x, y) ≠ s(c, z) := by
      intro ee
      rcases Sym2.eq_iff.1 ee with ⟨hh, _⟩ | ⟨_, hh⟩
      · exact hcx (congrArg ι hh.symm)
      · exact hcy (congrArg ι hh.symm)
    have du := sep x y e c u eu (de u)
    have dv := sep x y e c v ev (de v)
    have duv := sep c u eu c v ev (by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨_, he⟩ | ⟨he, _⟩
      · exact huv he
      · exact ev.ne he)
    exact no_four_neighbors G _ a b d f (splitB_max_three _) ea eb ed ef hab
      (distinct_incident _ _ _ du ha hd) (distinct_incident _ _ _ dv ha hf)
      (distinct_incident _ _ _ du hb hd) (distinct_incident _ _ _ dv hb hf)
      (distinct_incident _ _ _ duv hd hf)
  have no_share (x y x' y' : W) (e : H.Adj x y) (e' : H.Adj x' y')
      (different : s(x, y) ≠ s(x', y')) (z : V)
      (hz : z ∈ (P x y e).support) (hz' : z ∈ (P x' y' e').support)
      (hx : z ≠ ι x) (hy : z ≠ ι y) (hx' : z ≠ ι x') (hy' : z ≠ ι y') : False := by
    obtain ⟨a, b, hab, ea, eb, ha, hb⟩ := incident_internal (P x y e) (path _ _ _) hz hx hy
    obtain ⟨c, d, hcd, ec, ed, hc, hd⟩ := incident_internal (P x' y' e') (path _ _ _) hz' hx' hy'
    have dis := sep x y e x' y' e' different
    exact no_four_neighbors G z a b c d (splitB_max_three _) ea eb ec ed hab
      (distinct_incident _ _ _ dis ha hc) (distinct_incident _ _ _ dis ha hd)
      (distinct_incident _ _ _ dis hb hc) (distinct_incident _ _ _ dis hb hd) hcd
  let M : W → Set V
    | Sum.inl x => {ι (Sum.inl x)}
    | Sum.inr x => {z | z = ι (Sum.inr x) ∨
      ∃ y : ZMod q, ∃ e : H.Adj (Sum.inr x) (Sum.inl y), z ∈ (P (Sum.inr x) (Sum.inl y) e).dropLast.support}
  have start_mem (w : W) : ι w ∈ M w := by
    rcases w with w | w
    · rfl
    · exact .inl rfl
  have branch_case {w : W} {z : V} (hz : z ∈ M w) :
      z = ι w ∨ ∃ x y : ZMod q, ∃ e : H.Adj (Sum.inr x) (Sum.inl y),
        w = Sum.inr x ∧ z ∈ (P _ _ e).support ∧ z ≠ ι w ∧ z ≠ ι (Sum.inl y) := by
    by_cases he : z = ι w
    · exact .inl he
    · cases w with
      | inl x => exact (he hz).elim
      | inr x =>
        have hh : z = ι (Sum.inr x) ∨
            ∃ y : ZMod q, ∃ e : H.Adj (Sum.inr x) (Sum.inl y), z ∈ (P _ _ e).dropLast.support := hz
        obtain ⟨y, e, hp⟩ := hh.resolve_left he
        have hz' := dropped_internal (P _ _ e) (path _ _ _) (end_ne e) hp
        exact .inr ⟨x, y, e, rfl, hz'.1, he, hz'.2⟩
  refine ⟨M, ?_, ?_, ?_⟩
  · intro w
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
    refine ⟨⟨ι w, start_mem w⟩, ?_⟩
    rintro ⟨z, hz⟩
    by_cases h : z = ι w
    · have he : (⟨z, hz⟩ : M w) = ⟨ι w, start_mem w⟩ := Subtype.ext h
      rw [he]
    · cases w with
      | inl x => exact (h hz).elim
      | inr x =>
        have hh : z = ι (Sum.inr x) ∨
            ∃ y : ZMod q, ∃ e : H.Adj (Sum.inr x) (Sum.inl y), z ∈ (P _ _ e).dropLast.support := hz
        obtain ⟨y, e, hp⟩ := hh.resolve_left h
        let p := (P _ _ e).dropLast
        let pp := p.takeUntil z hp
        apply SimpleGraph.Walk.reachable (pp.induce (M (Sum.inr x)) ?_)
        intro v hv
        exact .inr ⟨y, e, p.support_takeUntil_subset_support hp hv⟩
  · intro w w' hne
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    rcases branch_case hz with h | ⟨x, y, e, hw, hp, hs, ht⟩ <;>
      rcases branch_case hz' with h' | ⟨x', y', e', hw', hp', hs', ht'⟩
    · exact hne (inj (h.symm.trans h'))
    · subst w'
      rw [h] at hp' hs' ht'
      exact no_image _ _ _ e' hp' hs' ht'
    · subst w
      rw [h'] at hp hs ht
      exact no_image _ _ _ e hp hs ht
    · subst w w'
      have hEdges : s(Sum.inr x, Sum.inl y) ≠ s(Sum.inr x', Sum.inl y') := by
        intro eq
        rcases Sym2.eq_iff.1 eq with ⟨he, _⟩ | ⟨he, _⟩
        · exact hne he
        · cases he
      exact no_share _ _ _ _ e e' hEdges z hp hp' hs ht hs' ht'
  · have edge_model (x y : ZMod q) (e : H.Adj (Sum.inr x) (Sum.inl y)) :
        ∃ u ∈ M (Sum.inr x), ∃ v ∈ M (Sum.inl y), G.Adj u v := by
      let p := P (Sum.inr x) (Sum.inl y) e
      have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne (end_ne e)
      have hm : p.penultimate ∈ p.dropLast.support := by
        rw [p.support_dropLast hn]
        exact SimpleGraph.Walk.penultimate_mem_dropLast_support hn
      exact ⟨p.penultimate, .inr ⟨y, e, hm⟩, ι (Sum.inl y), start_mem (Sum.inl y), SimpleGraph.Walk.adj_penultimate hn⟩
    rintro (x | x) (y | y) h
    · exact (splitB_not_inl_inl _ _ h).elim
    · obtain ⟨a, ha, b, hb, hab⟩ := edge_model y x h.symm
      exact ⟨b, hb, a, ha, hab.symm⟩
    · exact edge_model x y h
    · exact (splitB_not_inr_inr _ _ h).elim

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

-- Derive the strict opposite inequalities from the original congruence hypotheses.

private theorem inverse_characteristic {r n : ℕ} (hn : 1 < n)
    (hcop : Nat.Coprime n r) :
    0 < aInv n r ∧ aInv n r < n ∧ ∃ c : ℕ, r * aInv n r = 1 + c * n := by
  let _ : NeZero n := ⟨by omega⟩
  have hcast : ((r * aInv n r : ℕ) : ZMod n) = 1 := by
    unfold aInv
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one r hcop.symm
  have hmod : (r * aInv n r) % n = 1 := by
    have e := (ZMod.natCast_eq_natCast_iff' (r * aInv n r) 1 n).mp
      (by simpa only [Nat.cast_one] using hcast)
    simpa only [Nat.mod_eq_of_lt hn] using e
  let c := (r * aInv n r) / n
  have h : r * aInv n r = 1 + c * n := by
    have e := Nat.mod_add_div (r * aInv n r) n
    rw [hmod] at e
    simpa only [c, Nat.mul_comm n] using e.symm
  refine ⟨?_, ZMod.val_lt _, c, h⟩
  by_contra! hzero
  have ha : aInv n r = 0 := by omega
  simp [ha] at h <;> omega

private theorem inverse_unique {r n a : ℕ} (hn : 1 < n) (ha : a < n)
    (hcop : Nat.Coprime n r) (h : (r : ZMod n) * a = 1) :
    aInv n r = a := by
  let _ : NeZero n := ⟨by omega⟩
  have hinv := ZMod.coe_mul_inv_eq_one r hcop.symm
  have heq : (r : ZMod n)⁻¹ = a := by
    calc
      (r : ZMod n)⁻¹ = 1 * (r : ZMod n)⁻¹ := (one_mul _).symm
      _ = ((r : ZMod n) * a) * (r : ZMod n)⁻¹ := by rw [h]
      _ = (a : ZMod n) * ((r : ZMod n) * (r : ZMod n)⁻¹) := by ring
      _ = a := by rw [hinv, mul_one]
  unfold aInv
  rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt ha]

private theorem base_bounds {r q : ℕ} (hr : 2 ≤ r) (hq : 2 * r < q)
    (hq1 : (q : ZMod r) = 1) (hcop : Nat.Coprime q r) :
    ∃ k : ℕ, q = r * k + 1 ∧ dR q r ≤ k ∧ bR q r ≤ 2 * k + 1 := by
  let k := q / r
  have hmod : q % r = 1 := by
    have e := (ZMod.natCast_eq_natCast_iff' q 1 r).mp
      (by simpa only [Nat.cast_one] using hq1)
    simpa only [Nat.mod_eq_of_lt (show 1 < r by omega)] using e
  have hform : q = r * k + 1 := by
    have e := Nat.mod_add_div q r
    rw [hmod] at e
    simpa only [k, Nat.add_comm 1] using e.symm
  have hkpos : 0 < k := by
    change 0 < q / r
    exact Nat.div_pos (by omega) (by omega)
  have htwok : 2 * k ≤ r * k := Nat.mul_le_mul_right k hr
  have hkle : k ≤ q := by omega
  have hdiff : q - k < q := by omega
  have hinv : aInv q r = q - k := by
    apply inverse_unique (by omega) hdiff hcop
    have hc : (0 : ZMod q) = (r : ZMod q) * k + 1 := by
      have e := congrArg (fun n : ℕ => (n : ZMod q)) hform
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self] using e
    rw [Nat.cast_sub hkle, ZMod.natCast_self]
    linear_combination hc
  refine ⟨k, hform, ?_, ?_⟩
  · unfold dR
    rw [hinv]
    exact (min_le_right _ _).trans (by omega)
  · unfold bR
    rw [hinv]
    exact (min_le_right _ _).trans (by omega)

private theorem lift_bounds {r q m : ℕ} (hr : 2 ≤ r) (hq : 2 * r < q) (hm : 0 < m)
    (hq1 : (q : ZMod r) = 1) (hcop : Nat.Coprime (q * m) r)
    (hm1 : (m : ZMod r) ≠ 1) (hm2 : (m : ZMod r) ≠ -1) :
    2 * (q * m) ≤ r * (dR (q * m) r + 1) ∧ 4 * (q * m) ≤ r * (bR (q * m) r + 1) := by
  let n := q * m
  have hqn : q ≤ n := by
    dsimp [n]
    simpa only [mul_one] using Nat.mul_le_mul_left q (show 1 ≤ m by omega)
  obtain ⟨hapos, han, c, hc⟩ := inverse_characteristic (r := r) (n := n) (by omega) hcop
  let a := aInv n r
  change 0 < a at hapos
  change a < n at han
  change r * a = 1 + c * n at hc
  have hcast : (n : ZMod r) = m := by rw [show n = q * m from rfl, Nat.cast_mul, hq1, one_mul]
  have hc_mod : (0 : ZMod r) = 1 + (c : ZMod r) * (m : ZMod r) := by
    have e := congrArg (fun i : ℕ => (i : ZMod r)) hc
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_mul, hcast] using e
  have hc_pos : 0 < c := by
    by_contra! h
    have hc0 : c = 0 := by omega
    have hr2 : 2 ≤ r * a := by
      calc
        2 ≤ r := hr
        _ ≤ r * a := by simpa only [mul_one] using Nat.mul_le_mul_left r (show 1 ≤ a by omega)
    simp only [hc0, zero_mul, add_zero] at hc
    omega
  have hc_lt : c < r := by
    by_contra! h
    have hle := Nat.mul_le_mul_right n h
    have hlt := Nat.mul_lt_mul_of_pos_left han (show 0 < r by omega)
    omega
  have hc1 : c ≠ 1 := by
    intro he
    rw [he, Nat.cast_one, one_mul] at hc_mod
    apply hm2
    linear_combination -hc_mod
  have hcpred : c + 1 ≠ r := by
    intro he
    have hcz : (c : ZMod r) + 1 = 0 := by
      have e := congrArg (fun i : ℕ => (i : ZMod r)) he
      simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using e
    have hneg : (c : ZMod r) = -1 := by linear_combination hcz
    rw [hneg, neg_one_mul] at hc_mod
    apply hm1
    linear_combination hc_mod
  have hc_lower : 2 * n ≤ c * n := Nat.mul_le_mul_right n (by omega)
  have hc_upper : c * n + 2 * n ≤ r * n := calc
    c * n + 2 * n = (c + 2) * n := by ring
    _ ≤ r * n := Nat.mul_le_mul_right n (by omega)
  have hsum : r * (n - a) + r * a = r * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel han.le]
  have hA : 2 * n ≤ r * a := by omega
  have hB : 2 * n ≤ r * (n - a) + r := by omega
  change 2 * n ≤ r * (min a (n - a) + 1) ∧
    4 * n ≤ r * (min (2 * a - 1) (2 * n - 2 * a + 1) + 1)
  constructor
  · rcases le_total a (n - a) with h | h
    · rw [min_eq_left h, Nat.mul_add, Nat.mul_one]
      omega
    · rw [min_eq_right h, Nat.mul_add, Nat.mul_one]
      exact hB
  · rcases le_total (2 * a - 1) (2 * n - 2 * a + 1) with h | h
    · rw [min_eq_left h, show 2 * a - 1 + 1 = 2 * a by omega]
      calc
        4 * n ≤ 2 * (r * a) := by omega
        _ = r * (2 * a) := by ring
    · rw [min_eq_right h, show 2 * n - 2 * a + 1 + 1 = 2 * (n - a + 1) by omega]
      calc
        4 * n ≤ 2 * (r * (n - a) + r) := by omega
        _ = r * (2 * (n - a + 1)) := by simp only [Nat.mul_add, Nat.mul_one]; ring

private theorem distance_obstruction (r q m : ℕ) (hr : 2 ≤ r) (hm : 0 < m)
    (hq1 : (q : ZMod r) = 1) (hq : 4 * r ^ 2 < q + 2 * r) (hmr : Nat.Coprime m r)
    (hm1 : (m : ZMod r) ≠ 1) (hm2 : (m : ZMod r) ≠ -1) :
    (dR q r + 1) * (q * m) < (dR (q * m) r + 1) * q ∧
    (bR q r + 1) * (q * m) < (bR (q * m) r + 1) * q := by
  have hqgt : 2 * r < q := by
    nlinarith [Nat.mul_le_mul_left r (show 1 ≤ r by omega)]
  have hqr : Nat.Coprime q r := (ZMod.isUnit_iff_coprime q r).mp (by rw [hq1]; exact isUnit_one)
  have hnr : Nat.Coprime (q * m) r := (ZMod.isUnit_iff_coprime (q * m) r).mp (by
    rw [Nat.cast_mul, hq1, one_mul]
    exact (ZMod.isUnit_iff_coprime m r).mpr hmr)
  obtain ⟨k, hqform, hdq, hbq⟩ := base_bounds hr hqgt hq1 hqr
  obtain ⟨hdn, hbn⟩ := lift_bounds hr hqgt hm hq1 hnr hm1 hm2
  have huD : r * (dR q r + 1) < 2 * q := calc
    _ ≤ r * (k + 1) := Nat.mul_le_mul_left _ (by omega)
    _ < 2 * q := by rw [Nat.mul_add, Nat.mul_one]; omega
  have huB : r * (bR q r + 1) < 4 * q := calc
    _ ≤ r * (2 * k + 2) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (r * k) + 2 * r := by ring
    _ < 4 * q := by omega
  have compare (a b c : ℕ) (h1 : r * a < c * q) (h2 : c * (q * m) ≤ r * b) :
      a * (q * m) < b * q := by
    have hscaled : r * (a * m) < r * b := calc
      _ < c * (q * m) := by
        simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right h1 hm
      _ ≤ _ := h2
    have hab : a * m < b := by
      by_contra! h
      exact (not_le_of_gt hscaled) (Nat.mul_le_mul_left r h)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right hab (show 0 < q by omega)
  exact ⟨compare _ _ 2 huD hdn, compare _ _ 4 huB hbn⟩

private theorem minor_exclusion_given_distance (r q m : ℕ) (hr : 2 ≤ r) (hm : 0 < m)
    (hq1 : (q : ZMod r) = 1) (hq : 4 * r ^ 2 < q + 2 * r) (hmr : Nat.Coprime m r)
    (hm1 : (m : ZMod r) ≠ 1) (hm2 : (m : ZMod r) ≠ -1)
    (distance :
      (HadwigerConj.IsMinor (circulantD q r) (circulantD (q * m) r) →
        (dR (q * m) r + 1) * q ≤ (dR q r + 1) * (q * m)) ∧
      (HadwigerConj.IsMinor (splitB q r) (splitB (q * m) r) →
        (bR (q * m) r + 1) * q ≤ (bR q r + 1) * (q * m))) :
    ¬ HadwigerConj.IsMinor (circulantD q r) (circulantD (q * m) r) ∧
      ¬ HadwigerConj.IsMinor (splitB q r) (splitB (q * m) r) := by
  obtain ⟨hd, hb⟩ := distance_obstruction r q m hr hm hq1 hq hmr hm1 hm2
  exact ⟨fun h => (not_le_of_gt hd) (distance.1 h), fun h => (not_le_of_gt hb) (distance.2 h)⟩

end RobersonCx.ExclusionLocal

open RobersonCx RobersonCx.ExclusionLocal

theorem solution (r q m : ℕ) (hr : 2 ≤ r) (hq0 : 0 < q) (hm0 : 0 < m) (hq1 : (q : ZMod r) = 1)
    (hq : 4 * r ^ 2 < q + 2 * r) (hmr : Nat.Coprime m r) (hm1 : (m : ZMod r) ≠ 1)
    (hm2 : (m : ZMod r) ≠ -1) :
    ¬ HadwigerConj.IsMinor (circulantD q r) (circulantD (q * m) r) ∧
    ¬ HadwigerConj.IsMinor (splitB q r) (splitB (q * m) r) ∧
    ¬ IsImmersion (splitB q r) (splitB (q * m) r) := by
  have hqr : Nat.Coprime q r := (ZMod.isUnit_iff_coprime q r).1 (by rw [hq1]; exact isUnit_one)
  have hNr : Nat.Coprime (q * m) r := (ZMod.isUnit_iff_coprime (q * m) r).1 (by
    rw [Nat.cast_mul, hq1, one_mul]
    exact (ZMod.isUnit_iff_coprime m r).2 hmr)
  have hN : q ≤ q * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q (by omega : 1 ≤ m)
  have hqwide : 1 < q := by nlinarith [Nat.mul_le_mul_right r hr]
  obtain ⟨hD, hB⟩ := minor_exclusion_given_distance r q m hr hm0 hq1 hq hmr hm1 hm2
    ⟨distance_D r q (q * m) hr hq hN hqr hNr, distance_B r q (q * m) hr hq hN hqr hNr⟩
  exact ⟨hD, hB, fun himm => hB (splitB_immersion_minor hqwide (Nat.mul_pos hq0 hm0) himm)⟩
