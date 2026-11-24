-- Prove2me | solution 1 for WilliamsonShmoys.treewidth_disjoint_union_le
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T10:45:22.274804+00:00
-- url     : https://prove2.me/submissions/b465ce60-ccc6-4e95-8108-189a8df053c1

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

open SimpleGraph

namespace TwUnion

variable {k : ℕ} {T : Fin (k + 1) → Type}

/-- Disjoint union of the trees `t j`, with the chosen node `r j` of every copy `j ≠ 0`
joined to the chosen node `r 0` of copy `0`. -/
def rel (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (a b : Σ j, T j) : Prop :=
  (∃ j x y, a = ⟨j, x⟩ ∧ b = ⟨j, y⟩ ∧ (t j).Adj x y) ∨ (∃ j, j ≠ 0 ∧ a = ⟨j, r j⟩ ∧ b = ⟨0, r 0⟩)

def ug (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) : SimpleGraph (Σ j, T j) :=
  SimpleGraph.fromRel (rel t r)

lemma ug_same (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (j : Fin (k + 1)) (x y : T j) :
    (ug t r).Adj ⟨j, x⟩ ⟨j, y⟩ ↔ (t j).Adj x y := by
  constructor
  · intro h
    rw [ug, fromRel_adj] at h
    rcases h.2 with (⟨j', x', y', h1, h2, h3⟩ | ⟨j', hj, h1, h2⟩) |
        (⟨j', x', y', h1, h2, h3⟩ | ⟨j', hj, h1, h2⟩)
    · obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.mp h1
      obtain ⟨-, hy⟩ := Sigma.mk.inj_iff.mp h2
      cases hx; cases hy; exact h3
    · obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp h1
      obtain ⟨h0, -⟩ := Sigma.mk.inj_iff.mp h2
      exact absurd h0 hj
    · obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.mp h1
      obtain ⟨-, hy⟩ := Sigma.mk.inj_iff.mp h2
      cases hx; cases hy; exact h3.symm
    · obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp h1
      obtain ⟨h0, -⟩ := Sigma.mk.inj_iff.mp h2
      exact absurd h0 hj
  · intro h
    rw [ug, fromRel_adj]
    refine ⟨fun e => (t j).ne_of_adj h (eq_of_heq (Sigma.mk.inj_iff.mp e).2), ?_⟩
    exact Or.inl (Or.inl ⟨j, x, y, rfl, rfl, h⟩)

lemma ug_diff (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (a b : Σ j, T j) (hab : a.1 ≠ b.1)
    (h : (ug t r).Adj a b) :
    (a.1 ≠ 0 ∧ a = ⟨a.1, r a.1⟩ ∧ b = ⟨0, r 0⟩) ∨ (b.1 ≠ 0 ∧ b = ⟨b.1, r b.1⟩ ∧ a = ⟨0, r 0⟩) := by
  rw [ug, fromRel_adj] at h
  rcases h.2 with (⟨j', x', y', h1, h2, -⟩ | ⟨j', hj, h1, h2⟩) |
      (⟨j', x', y', h1, h2, -⟩ | ⟨j', hj, h1, h2⟩)
  · exact absurd (by rw [h1, h2]) hab
  · subst h1; subst h2; exact Or.inl ⟨hj, rfl, rfl⟩
  · exact absurd (by rw [h1, h2]) hab
  · subst h1; subst h2; exact Or.inr ⟨hj, rfl, rfl⟩

def emb (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (j : Fin (k + 1)) : t j →g ug t r :=
  ⟨fun x => ⟨j, x⟩, fun h => (ug_same t r j _ _).mpr h⟩

lemma emb_injective (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (j : Fin (k + 1)) :
    Function.Injective (emb t r j) := fun x y h => eq_of_heq (Sigma.mk.inj_iff.mp h).2

lemma ug_connected (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j) (ht : ∀ j, (t j).Connected) :
    (ug t r).Connected := by
  have hto : ∀ a : Σ j, T j, (ug t r).Reachable a ⟨0, r 0⟩ := by
    rintro ⟨j, x⟩
    have h1 : (ug t r).Reachable ⟨j, x⟩ ⟨j, r j⟩ := ((ht j).preconnected x (r j)).map (emb t r j)
    by_cases hj : j = 0
    · subst hj; exact h1
    · refine h1.trans (Adj.reachable ?_)
      rw [ug, fromRel_adj]
      refine ⟨fun e => hj (Sigma.mk.inj_iff.mp e).1, Or.inl (Or.inr ⟨j, hj, rfl, rfl⟩)⟩
  haveI : Nonempty (Σ j, T j) := ⟨⟨0, r 0⟩⟩
  exact ⟨fun a b => (hto a).trans (hto b).symm⟩

lemma ug_isTree [∀ j, Finite (T j)] (t : ∀ j, SimpleGraph (T j)) (r : ∀ j, T j)
    (ht : ∀ j, (t j).IsTree) : (ug t r).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨ug_connected t r (fun j => (ht j).connected), ?_⟩
  have h1 : ∀ j, Nat.card (t j).edgeSet + 1 = Nat.card (T j) :=
    fun j => (isTree_iff_connected_and_card.mp (ht j)).2
  let f : (Σ j, (t j).edgeSet) ⊕ {j : Fin (k + 1) // j ≠ 0} → (ug t r).edgeSet := fun
    | Sum.inl ⟨j, e⟩ => ⟨Sym2.map (Sigma.mk j) e.1, by
        obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | h x y => simpa [Sym2.map_mk, ug_same] using he⟩
    | Sum.inr j => ⟨s(⟨j.1, r j.1⟩, ⟨0, r 0⟩), by
        rw [mem_edgeSet, ug, fromRel_adj]
        exact ⟨fun e => j.2 (Sigma.mk.inj_iff.mp e).1, Or.inl (Or.inr ⟨j.1, j.2, rfl, rfl⟩)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (⟨j, ⟨e, he⟩⟩ | ⟨j, hj⟩) (⟨j', ⟨e', he'⟩⟩ | ⟨j', hj'⟩) h
      · simp only [f, Subtype.mk.injEq] at h
        induction e using Sym2.ind with
        | h x y =>
          induction e' using Sym2.ind with
          | h x' y' =>
            simp only [Sym2.map_mk, Sym2.eq_iff] at h
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.mp h1
              obtain ⟨-, hy⟩ := Sigma.mk.inj_iff.mp h2
              cases hx; cases hy; rfl
            · obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.mp h1
              obtain ⟨-, hy⟩ := Sigma.mk.inj_iff.mp h2
              cases hx; cases hy
              congr 2
              exact Subtype.ext Sym2.eq_swap
      · exfalso
        simp only [f, Subtype.mk.injEq] at h
        induction e using Sym2.ind with
        | h x y =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := (Sigma.mk.inj_iff.mp h1).1; have := (Sigma.mk.inj_iff.mp h2).1
            subst_vars; exact hj' rfl
          · have := (Sigma.mk.inj_iff.mp h1).1; have := (Sigma.mk.inj_iff.mp h2).1
            subst_vars; exact hj' rfl
      · exfalso
        simp only [f, Subtype.mk.injEq] at h
        induction e' using Sym2.ind with
        | h x y =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := (Sigma.mk.inj_iff.mp h1).1; have := (Sigma.mk.inj_iff.mp h2).1
            subst_vars; exact hj rfl
          · have := (Sigma.mk.inj_iff.mp h1).1; have := (Sigma.mk.inj_iff.mp h2).1
            subst_vars; exact hj rfl
      · simp only [f, Subtype.mk.injEq, Sym2.eq_iff] at h
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · have := (Sigma.mk.inj_iff.mp h1).1
          subst this; rfl
        · exact absurd (Sigma.mk.inj_iff.mp h1).1 hj
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h a b =>
        rcases a with ⟨ja, x⟩
        rcases b with ⟨jb, y⟩
        by_cases hab : ja = jb
        · subst hab
          rw [mem_edgeSet, ug_same] at he
          exact ⟨Sum.inl ⟨ja, ⟨s(x, y), he⟩⟩, by simp [f, Sym2.map_mk]⟩
        · rcases ug_diff t r ⟨ja, x⟩ ⟨jb, y⟩ hab he with ⟨hj, h1, h2⟩ | ⟨hj, h1, h2⟩
          · refine ⟨Sum.inr ⟨ja, hj⟩, ?_⟩
            simp only [f, Subtype.mk.injEq]
            rw [h1, h2]
          · refine ⟨Sum.inr ⟨jb, hj⟩, ?_⟩
            simp only [f, Subtype.mk.injEq]
            rw [h1, h2, Sym2.eq_swap]
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sum, Nat.card_sigma] at hc
  rw [← hc, Nat.card_sigma]
  have hk : Nat.card {j : Fin (k + 1) // j ≠ 0} = k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
    simp
  rw [hk, ← Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib]
  simp
  omega

end TwUnion

theorem solution {m n : ℕ} (H : Fin m → SimpleGraph (Fin n)) (w : ℕ)
    (h : ∀ j, RobertsonSeymour1986.GM5.TreewidthLE (H j) w) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)) w := by
  classical
  rcases m with _ | k
  · -- no vertices: a one-node tree with an empty bag
    refine ⟨Unit, inferInstance, ⊥, fun _ => ∅, ⟨?_, ?_, ?_, ?_⟩, fun _ => by simp⟩
    · exact ⟨⟨fun a b => by cases a; cases b; rfl⟩, fun v c hc => by
        cases c with
        | nil => exact hc.ne_nil rfl
        | cons hadj _ => exact absurd hadj (by simp)⟩
    · intro v; exact v.1.elim0
    · intro x y _; exact x.1.elim0
    · intro s s' s'' p _ _; simp
  · choose T instT t X hdec hwidth using h
    have htree : ∀ j, (t j).IsTree := fun j => (hdec j).1
    have r : ∀ j, T j := fun j => Classical.choice (htree j).connected.nonempty
    let G' := TwUnion.ug t r
    have hG' : G'.IsTree := TwUnion.ug_isTree t r htree
    let ι : ∀ j : Fin (k + 1), Fin n ↪ Fin (k + 1) × Fin n := fun j =>
      ⟨fun a => (j, a), fun a b e => congrArg Prod.snd e⟩
    let X' : (Σ j, T j) → Finset (Fin (k + 1) × Fin n) := fun s => (X s.1 s.2).map (ι s.1)
    refine ⟨Σ j, T j, inferInstance, G', X', ⟨hG', ?_, ?_, ?_⟩, ?_⟩
    · rintro ⟨j, a⟩
      obtain ⟨s, hs⟩ := (hdec j).2.1 a
      exact ⟨⟨j, s⟩, Finset.mem_map.mpr ⟨a, hs, rfl⟩⟩
    · rintro ⟨j, a⟩ ⟨j', b⟩ hadj
      rw [SimpleGraph.fromRel_adj] at hadj
      have key : ∀ (j : Fin (k + 1)) (a b : Fin n), (H j).Adj a b →
          ∃ s, (j, a) ∈ X' s ∧ (j, b) ∈ X' s := by
        intro j a b hab
        obtain ⟨s, h1, h2⟩ := (hdec j).2.2.1 a b hab
        exact ⟨⟨j, s⟩, Finset.mem_map.mpr ⟨a, h1, rfl⟩, Finset.mem_map.mpr ⟨b, h2, rfl⟩⟩
      rcases hadj.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2; subst h1; exact key j a b h2
      · simp only at h1 h2; subst h1
        obtain ⟨s, hs1, hs2⟩ := key j' b a h2
        exact ⟨s, hs2, hs1⟩
    · rintro ⟨j, x⟩ s' ⟨j', y⟩ p hp hs' v hv
      rw [Finset.mem_inter] at hv
      obtain ⟨hv1, hv2⟩ := hv
      simp only [X', Finset.mem_map] at hv1 hv2
      obtain ⟨a, ha, rfl⟩ := hv1
      obtain ⟨b, hb, hab⟩ := hv2
      simp only [ι, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨q, hq, -⟩ := (htree j).existsUnique_path x y
      have hqm : (q.map (TwUnion.emb t r j)).IsPath := hq.map (TwUnion.emb_injective t r j)
      have hpq : p = q.map (TwUnion.emb t r j) := (hG'.existsUnique_path _ _).unique hp hqm
      have hs2 : s' ∈ (q.map (TwUnion.emb t r j)).support := by rw [← hpq]; exact hs'
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hs2
      obtain ⟨c, hc, rfl⟩ := hs2
      have := (hdec j).2.2.2 x c y q hq hc (Finset.mem_inter.mpr ⟨ha, hb⟩)
      exact Finset.mem_map.mpr ⟨a, this, rfl⟩
    · rintro ⟨j, x⟩
      simpa [X'] using hwidth j x
