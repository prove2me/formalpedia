-- Prove2me | solution 1 for RobersonCx.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-27T01:43:57.908163+00:00
-- url     : https://prove2.me/submissions/cf6ca24c-4783-4981-98cf-8e608be78038

import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx.ExclusionLocal

open scoped Classical

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

end RobersonCx.ExclusionLocal

namespace RobersonCx.ExclusionLocal

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

open RobersonCx RobersonCx.ExclusionLocal

theorem solution (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    PwLE (splitB n r) (2 * r) ∧
    (∀ a : ZMod n,
      PwLE ((splitB n r).induce
        ({x | ∃ j < r, x = Sum.inl (a + (j : ZMod n))} : Set (ZMod n ⊕ ZMod n))ᶜ) r ∧
      PwLE ((splitB n r).induce
        ({x | ∃ j < r, x = Sum.inr (a + (j : ZMod n))} : Set (ZMod n ⊕ ZMod n))ᶜ) r) ∧
    (∀ i : ZMod n,
      PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl i)}) (2 * r - 1) ∧
      PwLE ((splitB n r).deleteEdges {s(Sum.inr i, Sum.inl (i + (r : ZMod n)))}) (2 * r - 1)) := by
  classical
  have : NeZero n := ⟨by omega⟩
  let leftBlock (a : ZMod n) : Set (ZMod n ⊕ ZMod n) :=
    {x | ∃ j < r, x = Sum.inl (a + (j : ZMod n))}
  let rightBlock (a : ZMod n) : Set (ZMod n ⊕ ZMod n) :=
    {x | ∃ j < r, x = Sum.inr (a + (j : ZMod n))}
  have left_eq (a : ZMod n) : uWindow a (Finset.range r) = leftBlock a := by
    ext x
    cases x with
    | inl x =>
      change coordinate a x ∈ Finset.range r ↔ ∃ j < r, Sum.inl x = Sum.inl (a + (j : ZMod n))
      simp only [Finset.mem_range, Sum.inl.injEq]
      constructor
      · intro hx
        exact ⟨coordinate a x, hx, (coordinate_spec a x).symm⟩
      · rintro ⟨j, hj, rfl⟩
        simpa only [coordinate, add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega : j < n)] using hj
    | inr x => simp [uWindow, leftBlock]
  have left_width (a : ZMod n) : PwLE ((splitB n r).induce (leftBlock a)ᶜ) r := by
    rw [← left_eq a]
    exact pathwidth_B_delete_u hr hn a
  have right_width (a : ZMod n) : PwLE ((splitB n r).induce (rightBlock a)ᶜ) r := by
    let o := -(a + ((r - 1 : ℕ) : ZMod n))
    have coord_reversal (j : ℕ) (hj : j < r) :
        -(a + (j : ZMod n)) = o + ((r - 1 - j : ℕ) : ZMod n) := by
      dsimp [o]
      rw [Nat.cast_sub (by omega : j ≤ r - 1)]
      abel
    have belongs (x : ZMod n ⊕ ZMod n) : x ∈ rightBlock a ↔ flipB x ∈ leftBlock o := by
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨r - 1 - j, by omega, congrArg Sum.inl (coord_reversal j hj)⟩
      · rintro ⟨j, hj, he⟩
        have hk : r - 1 - j < r := by omega
        have hdouble : r - 1 - (r - 1 - j) = j := by omega
        have hf : flipB (Sum.inr (a + ((r - 1 - j : ℕ) : ZMod n))) = Sum.inl (o + (j : ZMod n)) := by
          change Sum.inl (-(a + ((r - 1 - j : ℕ) : ZMod n))) = _
          rw [coord_reversal _ hk, hdouble]
        exact ⟨r - 1 - j, hk, flipB_invol.injective (he.trans hf.symm)⟩
    let f : ↑((rightBlock a)ᶜ : Set (ZMod n ⊕ ZMod n)) → ↑((leftBlock o)ᶜ : Set (ZMod n ⊕ ZMod n)) :=
      fun x => ⟨flipB x.val, fun hx => x.property ((belongs _).2 hx)⟩
    have hf : Function.Injective f := fun x y he =>
      Subtype.ext (flipB_invol.injective (congrArg Subtype.val he))
    exact pathwidth_of_injection f hf (fun _ _ h => flipB_adj _ _ h) (left_width o)
  have cardLeft : (leftBlock 0).ncard ≤ r := by
    rw [← left_eq]
    simpa only [Finset.card_range] using uWindow_card (0 : ZMod n) (Finset.range r)
  refine ⟨?_, fun a => ⟨left_width a, right_width a⟩, fun i => ⟨?_, pathwidth_B_delete_long hr hn i⟩⟩
  · simpa only [two_mul] using pathwidth_add_vertices (splitB n r) (leftBlock 0) r r cardLeft (left_width 0)
  · have flipEdge : s(Sum.inr i, Sum.inl i) = s(Sum.inl i, Sum.inr i) :=
      Sym2.eq_iff.2 (.inr ⟨rfl, rfl⟩)
    rw [flipEdge]
    exact pathwidth_B_delete_spoke hr hn i
