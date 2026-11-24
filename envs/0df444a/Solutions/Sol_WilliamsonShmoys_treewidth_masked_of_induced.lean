-- Prove2me | solution 1 for WilliamsonShmoys.treewidth_masked_of_induced
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:56:07.927861+00:00
-- url     : https://prove2.me/submissions/e75e9ee3-2bf6-4481-821a-832e1c1ec291

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

open SimpleGraph

namespace TwMask

variable {T W : Type}

/-- Relation for the tree `t` with every element of `W` hung as a leaf below `t0`. -/
def rel (t : SimpleGraph T) (t0 : T) (a b : T ⊕ W) : Prop :=
  (∃ x y, a = Sum.inl x ∧ b = Sum.inl y ∧ t.Adj x y) ∨ (∃ w, a = Sum.inr w ∧ b = Sum.inl t0)

def tg (t : SimpleGraph T) (t0 : T) : SimpleGraph (T ⊕ W) := SimpleGraph.fromRel (rel t t0)

lemma tg_inl_inl (t : SimpleGraph T) (t0 : T) (x y : T) :
    (tg (W := W) t t0).Adj (Sum.inl x) (Sum.inl y) ↔ t.Adj x y := by
  constructor
  · intro h
    rw [tg, fromRel_adj] at h
    rcases h.2 with (⟨x', y', h1, h2, h3⟩ | ⟨w, h1, _⟩) | (⟨x', y', h1, h2, h3⟩ | ⟨w, h1, _⟩)
    · rw [Sum.inl_injective h1, Sum.inl_injective h2]; exact h3
    · cases h1
    · rw [Sum.inl_injective h1, Sum.inl_injective h2]; exact h3.symm
    · cases h1
  · intro h
    rw [tg, fromRel_adj]
    exact ⟨fun e => t.ne_of_adj h (Sum.inl_injective e), Or.inl (Or.inl ⟨x, y, rfl, rfl, h⟩)⟩

lemma tg_inr_inl (t : SimpleGraph T) (t0 : T) (w : W) (y : T) :
    (tg t t0).Adj (Sum.inr w) (Sum.inl y) ↔ y = t0 := by
  constructor
  · intro h
    rw [tg, fromRel_adj] at h
    rcases h.2 with (⟨x', y', h1, _, _⟩ | ⟨w', _, h2⟩) | (⟨x', y', _, h2, _⟩ | ⟨w', h1, _⟩)
    · cases h1
    · exact Sum.inl_injective h2
    · cases h2
    · cases h1
  · rintro rfl
    rw [tg, fromRel_adj]
    exact ⟨Sum.inr_ne_inl, Or.inl (Or.inr ⟨w, rfl, rfl⟩)⟩

lemma tg_inr_inr (t : SimpleGraph T) (t0 : T) (w w' : W) :
    ¬ (tg t t0).Adj (Sum.inr w) (Sum.inr w') := by
  intro h
  rw [tg, fromRel_adj] at h
  rcases h.2 with (⟨x', y', h1, _, _⟩ | ⟨w'', _, h2⟩) | (⟨x', y', h1, _, _⟩ | ⟨w'', _, h2⟩)
  · cases h1
  · cases h2
  · cases h1
  · cases h2

def emb (t : SimpleGraph T) (t0 : T) : t →g (tg (W := W) t t0) :=
  ⟨Sum.inl, fun h => (tg_inl_inl t t0 _ _).mpr h⟩

lemma emb_injective (t : SimpleGraph T) (t0 : T) :
    Function.Injective (emb (W := W) t t0) := Sum.inl_injective

lemma tg_connected (t : SimpleGraph T) (t0 : T) (ht : t.Connected) :
    (tg (W := W) t t0).Connected := by
  have hto : ∀ a : T ⊕ W, (tg t t0).Reachable a (Sum.inl t0) := by
    rintro (x | w)
    · exact (ht.preconnected x t0).map (emb t t0)
    · exact ((tg_inr_inl t t0 w t0).mpr rfl).reachable
  haveI : Nonempty (T ⊕ W) := ⟨Sum.inl t0⟩
  exact ⟨fun a b => (hto a).trans (hto b).symm⟩

lemma tg_isTree [Finite T] [Finite W] (t : SimpleGraph T) (t0 : T) (ht : t.IsTree) :
    (tg (W := W) t t0).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨tg_connected t t0 ht.connected, ?_⟩
  have h1 := (isTree_iff_connected_and_card.mp ht).2
  -- edges of tg ≃ edges of t ⊕ W
  let f : t.edgeSet ⊕ W → (tg (W := W) t t0).edgeSet := fun
    | Sum.inl e => ⟨Sym2.map Sum.inl e.1, by
        obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | h x y => simpa [Sym2.map_mk, tg_inl_inl] using he⟩
    | Sum.inr w => ⟨s(Sum.inr w, Sum.inl t0), by
        simp [tg_inr_inl]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (⟨e, he⟩ | w) (⟨e', he'⟩ | w') h
      · simp only [f, Subtype.mk.injEq] at h
        have := Sym2.map.injective Sum.inl_injective h
        subst this; rfl
      · exfalso
        simp only [f, Subtype.mk.injEq] at h
        induction e using Sym2.ind with
        | h x y =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨h, -⟩ | ⟨-, h⟩ <;> cases h
      · exfalso
        simp only [f, Subtype.mk.injEq] at h
        induction e' using Sym2.ind with
        | h x y =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
      · simp only [f, Subtype.mk.injEq, Sym2.eq_iff] at h
        rcases h with ⟨h, -⟩ | ⟨h, -⟩
        · cases h; rfl
        · cases h
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h a b =>
        rcases a with x | w <;> rcases b with y | w'
        · rw [mem_edgeSet, tg_inl_inl] at he
          exact ⟨Sum.inl ⟨s(x, y), he⟩, by simp [f, Sym2.map_mk]⟩
        · rw [mem_edgeSet] at he
          have := (tg_inr_inl t t0 w' x).mp he.symm
          subst this
          exact ⟨Sum.inr w', by simp [f, Sym2.eq_swap]⟩
        · rw [mem_edgeSet] at he
          have := (tg_inr_inl t t0 w y).mp he
          subst this
          exact ⟨Sum.inr w, by simp [f]⟩
        · exact absurd he (tg_inr_inr t t0 w w')
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sum] at hc
  rw [← hc, Nat.card_sum]
  omega

end TwMask

theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (w : ℕ)
    (h : RobertsonSeymour1986.GM5.TreewidthLE (G.induce {v | P v}) w) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun u v => G.Adj u v ∧ P u ∧ P v)) w := by
  classical
  obtain ⟨T, instT, t, X, ⟨htree, hcov, hedge, hpath⟩, hwidth⟩ := h
  let S := {v : Fin n | P v}
  let W := {v : Fin n // ¬ P v}
  obtain ⟨t0⟩ := htree.connected.nonempty
  have ht' : (TwMask.tg (W := W) t t0).IsTree := TwMask.tg_isTree t t0 htree
  let ι : S ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  let X' : T ⊕ W → Finset (Fin n) := fun
    | Sum.inl s => (X s).map ι
    | Sum.inr v => {v.1}
  refine ⟨T ⊕ W, inferInstance, TwMask.tg (W := W) t t0, X', ⟨ht', ?_, ?_, ?_⟩, ?_⟩
  · intro v
    by_cases hv : P v
    · obtain ⟨s, hs⟩ := hcov ⟨v, hv⟩
      exact ⟨Sum.inl s, Finset.mem_map.mpr ⟨⟨v, hv⟩, hs, rfl⟩⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, Finset.mem_singleton_self _⟩
  · intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    obtain ⟨hne, hr⟩ := hxy
    have key : ∀ a b : Fin n, G.Adj a b ∧ P a ∧ P b → ∃ s, a ∈ X' s ∧ b ∈ X' s := by
      rintro a b ⟨hab, ha, hb⟩
      obtain ⟨s, hs1, hs2⟩ := hedge ⟨a, ha⟩ ⟨b, hb⟩ (by simpa using hab)
      exact ⟨Sum.inl s, Finset.mem_map.mpr ⟨_, hs1, rfl⟩, Finset.mem_map.mpr ⟨_, hs2, rfl⟩⟩
    rcases hr with h | h
    · exact key x y h
    · obtain ⟨s, h1, h2⟩ := key y x h
      exact ⟨s, h2, h1⟩
  · intro s s' s'' p hp hs' x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases s with a | wa <;> rcases s'' with b | wb
    · -- both tree nodes: p is the image of the t-path
      simp only [X', Finset.mem_map] at hx1 hx2
      obtain ⟨y, hy, rfl⟩ := hx1
      obtain ⟨y', hy', hyy⟩ := hx2
      have hyy' : y' = y := ι.injective hyy
      subst hyy'
      obtain ⟨q, hq, -⟩ := htree.existsUnique_path a b
      have hqm : (q.map (TwMask.emb (W := W) t t0)).IsPath :=
        hq.map (TwMask.emb_injective t t0)
      have hpq : p = q.map (TwMask.emb t t0) :=
        (ht'.existsUnique_path _ _).unique hp hqm
      have hs2 : s' ∈ (q.map (TwMask.emb (W := W) t t0)).support := by
        rw [← hpq]; exact hs'
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hs2
      obtain ⟨c, hc, rfl⟩ := hs2
      have := hpath a c b q hq hc (Finset.mem_inter.mpr ⟨hy, hy'⟩)
      exact Finset.mem_map.mpr ⟨_, this, rfl⟩
    · exfalso
      simp only [X', Finset.mem_map, Finset.mem_singleton] at hx1 hx2
      obtain ⟨y, -, rfl⟩ := hx1
      exact wb.2 (hx2 ▸ y.2)
    · exfalso
      simp only [X', Finset.mem_map, Finset.mem_singleton] at hx1 hx2
      obtain ⟨y, -, rfl⟩ := hx2
      exact wa.2 (hx1 ▸ y.2)
    · simp only [X', Finset.mem_singleton] at hx1 hx2
      have hw : wa = wb := Subtype.ext (hx1.symm.trans hx2)
      subst hw
      have := (SimpleGraph.Walk.isPath_iff_nil.mp hp).eq_nil
      subst this
      simp at hs'
      subst hs'
      simpa [X'] using hx1
  · rintro (s | v)
    · simpa [X'] using hwidth s
    · simp [X']
