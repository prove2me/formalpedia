-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.treewidthLE_of_finite_partition_decompositions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:48:05.924689+00:00
-- url     : https://prove2.me/submissions/3fec9109-9dda-4724-92f6-0c6953d43009

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

namespace A3S55FPD

open SimpleGraph

theorem not_reach {V : Type} (G : SimpleGraph V) (f : V → Prop) (u v : V) (hu : f u) (hv : ¬ f v)
    (h : ∀ x y, G.Adj x y → s(x, y) ≠ s(u, v) → (f x → f y)) :
    ¬ (G.deleteEdges {s(u, v)}).Reachable u v := by
  rintro ⟨p⟩
  have key : ∀ x y (q : (G.deleteEdges {s(u, v)}).Walk x y), f x → f y := by
    intro x y q
    induction q with
    | nil => exact id
    | cons hadj _ ih =>
      intro hx
      rw [deleteEdges_adj] at hadj
      exact ih (h _ _ hadj.1 (by simpa using hadj.2) hx)
  exact hv (key _ _ p hu)

variable {ι : Type} (T : ι → Type) (t : ∀ i, SimpleGraph (T i)) (r : ∀ i, T i)

def rel (x y : Option (Σ i, T i)) : Prop :=
  (∃ i a b, x = some ⟨i, a⟩ ∧ y = some ⟨i, b⟩ ∧ (t i).Adj a b) ∨
    (∃ i, x = none ∧ y = some ⟨i, r i⟩)

def glue : SimpleGraph (Option (Σ i, T i)) := SimpleGraph.fromRel (rel T t r)

theorem glue_adj (x y : Option (Σ i, T i)) :
    (glue T t r).Adj x y ↔ x ≠ y ∧ (rel T t r x y ∨ rel T t r y x) := by
  simp [glue, SimpleGraph.fromRel_adj]

def emb (i : ι) : t i →g glue T t r where
  toFun a := some ⟨i, a⟩
  map_rel' := by
    intro a b h
    rw [glue_adj]
    refine ⟨?_, Or.inl (Or.inl ⟨i, a, b, rfl, rfl, h⟩)⟩
    intro he
    simp at he
    exact h.ne he

theorem emb_inj (i : ι) : Function.Injective (emb T t r i) := by
  intro a b h
  simpa [emb] using h

theorem glue_connected (ht : ∀ i, (t i).IsTree) : (glue T t r).Connected := by
  have hreach : ∀ x, (glue T t r).Reachable none x := by
    rintro (_ | ⟨i, a⟩)
    · exact Reachable.refl _
    · have h1 : (glue T t r).Reachable none (some ⟨i, r i⟩) := by
        refine Adj.reachable ?_
        rw [glue_adj]
        exact ⟨by simp, Or.inl (Or.inr ⟨i, rfl, rfl⟩)⟩
      have h2 : (glue T t r).Reachable (some ⟨i, r i⟩) (some ⟨i, a⟩) :=
        ((ht i).connected (r i) a).map (emb T t r i)
      exact h1.trans h2
  exact Connected.mk (fun x y => (hreach x).symm.trans (hreach y))

theorem bridge_of_rel (ht : ∀ i, (t i).IsTree) (x y : Option (Σ i, T i)) (hr : rel T t r x y) :
    ¬ ((glue T t r).deleteEdges {s(x, y)}).Reachable x y := by
  -- reduce to iff-preservation along base relation
  suffices H : ∃ f : Option (Σ i, T i) → Prop, f x ∧ ¬ f y ∧
      ∀ u v, rel T t r u v → s(u, v) ≠ s(x, y) → (f u ↔ f v) by
    obtain ⟨f, hx, hy, hf⟩ := H
    refine not_reach _ f x y hx hy ?_
    intro u v huv hne
    rw [glue_adj] at huv
    rcases huv.2 with h | h
    · exact (hf u v h hne).1
    · exact (hf v u h (by rwa [Sym2.eq_swap])).2
  rcases hr with ⟨i, a, b, rfl, rfl, hab⟩ | ⟨i, rfl, rfl⟩
  · let R : T i → Prop := fun c => ((t i).deleteEdges {s(a, b)}).Reachable a c
    have hRb : ¬ R b := by
      have := (isAcyclic_iff_forall_adj_isBridge.1 (ht i).isAcyclic) hab
      rwa [isBridge_iff] at this
    refine ⟨fun z => (∃ c, z = some ⟨i, c⟩ ∧ R c) ∨ ((∀ c, z ≠ some ⟨i, c⟩) ∧ R (r i)),
      Or.inl ⟨a, rfl, Reachable.refl _⟩, ?_, ?_⟩
    · rintro (⟨c, hc, hR⟩ | ⟨hne, _⟩)
      · simp at hc
        subst hc
        exact hRb hR
      · exact hne b rfl
    · rintro u v (⟨j, c, d, rfl, rfl, hcd⟩ | ⟨j, rfl, rfl⟩) hne
      · by_cases hj : j = i
        · subst hj
          have hcd' : ((t j).deleteEdges {s(a, b)}).Adj c d := by
            rw [deleteEdges_adj]
            refine ⟨hcd, ?_⟩
            intro hmem
            simp only [Set.mem_singleton_iff] at hmem
            apply hne
            rcases Sym2.eq_iff.1 hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Sym2.eq_swap
          simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and, exists_eq_left',
            ne_eq, forall_eq', false_and, or_false]
          exact ⟨fun h => h.trans hcd'.reachable, fun h => h.trans hcd'.reachable.symm⟩
        · have h1 : ∀ e : T j, ∀ c', (some ⟨j, e⟩ : Option (Σ i, T i)) ≠ some ⟨i, c'⟩ := by
            intro e c' h
            simp at h
            exact hj h.1
          constructor
          · rintro (⟨c', hc', _⟩ | ⟨_, h⟩)
            · exact absurd hc' (h1 _ _)
            · exact Or.inr ⟨h1 _, h⟩
          · rintro (⟨c', hc', _⟩ | ⟨_, h⟩)
            · exact absurd hc' (h1 _ _)
            · exact Or.inr ⟨h1 _, h⟩
      · by_cases hj : j = i
        · subst hj
          simp
        · have h1 : ∀ c', (some ⟨j, r j⟩ : Option (Σ i, T i)) ≠ some ⟨i, c'⟩ := by
            intro c' h
            simp at h
            exact hj h.1
          simp only [reduceCtorEq, false_and, exists_false, ne_eq, not_false_eq_true,
            implies_true, true_and, false_or]
          exact ⟨fun h => Or.inr ⟨h1, h⟩, fun h => h.elim (fun ⟨c', hc', _⟩ => absurd hc' (h1 c'))
            (fun h => h.2)⟩
  · refine ⟨fun z => ¬ ∃ c, z = some ⟨i, c⟩, ?_, ?_, ?_⟩
    · simp
    · simp
    · rintro u v (⟨j, c, d, rfl, rfl, hcd⟩ | ⟨j, rfl, rfl⟩) hne <;> refine not_congr ?_
      · simp only [Option.some.injEq, Sigma.mk.injEq]
        constructor
        · rintro ⟨_, rfl, _⟩; exact ⟨d, rfl, HEq.rfl⟩
        · rintro ⟨_, rfl, _⟩; exact ⟨c, rfl, HEq.rfl⟩
      · by_cases hj : j = i
        · subst hj; exact absurd rfl hne
        · simp only [reduceCtorEq, exists_false, Option.some.injEq, Sigma.mk.injEq, false_iff,
            not_exists, not_and]
          intro _ h; exact absurd h hj

theorem glue_isTree (ht : ∀ i, (t i).IsTree) : (glue T t r).IsTree := by
  refine ⟨glue_connected T t r ht, ?_⟩
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rw [isBridge_iff]
  rw [glue_adj] at hxy
  rcases hxy.2 with h | h
  · exact bridge_of_rel T t r ht x y h
  · rw [Sym2.eq_swap]
    exact fun h' => bridge_of_rel T t r ht y x h h'.symm

end A3S55FPD

open A3S55FPD in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) (ι : Type) [Fintype ι] (C : ι → Finset V) (hcover : ∀ v : V, ∃ i, v ∈ C i) (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hedge : ∀ x y : V, G.Adj x y → ∃ i, x ∈ C i ∧ y ∈ C i) (hdecomps : ∀ i, ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T) (X : T → Finset {u : V // u ∈ C i}), RobertsonSeymour1986.GM5.IsTreeDecomposition (G.induce {u : V | u ∈ C i}) t X ∧ ∀ s : T, (X s).card ≤ w + 1) : RobertsonSeymour1986.GM5.TreewidthLE G w := by
  classical
  choose T hT t X hX hcard using hdecomps
  have hr : ∀ i, Nonempty (T i) := fun i => (hX i).1.connected.nonempty
  let r : ∀ i, T i := fun i => Classical.choice (hr i)
  let X' : Option (Σ i, T i) → Finset V := fun z =>
    match z with
    | none => ∅
    | some ⟨i, a⟩ => (X i a).map (Function.Embedding.subtype _)
  have htree : (glue T t r).IsTree := glue_isTree T t r (fun i => (hX i).1)
  refine ⟨Option (Σ i, T i), inferInstance, glue T t r, X', ⟨htree, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨i, hi⟩ := hcover v
    obtain ⟨a, ha⟩ := (hX i).2.1 ⟨v, hi⟩
    exact ⟨some ⟨i, a⟩, Finset.mem_map.2 ⟨_, ha, rfl⟩⟩
  · intro x y hxy
    obtain ⟨i, hx, hy⟩ := hedge x y hxy
    obtain ⟨a, ha, hb⟩ := (hX i).2.2.1 ⟨x, hx⟩ ⟨y, hy⟩ (by simpa using hxy)
    exact ⟨some ⟨i, a⟩, Finset.mem_map.2 ⟨_, ha, rfl⟩, Finset.mem_map.2 ⟨_, hb, rfl⟩⟩
  · rintro (_ | ⟨i, a⟩) s' (_ | ⟨j, b⟩) p hp hs'
    · simp [X']
    · simp [X']
    · simp [X']
    · obtain rfl | hij := eq_or_ne i j
      · obtain ⟨q, hq⟩ := (hX i).1.connected.exists_isPath a b
        have hq' : (q.map (emb T t r i)).IsPath := hq.map (emb_inj T t r i)
        have hpq : p = q.map (emb T t r i) :=
          (htree.existsUnique_path _ _).unique hp hq'
        have hsupp : p.support = q.support.map (emb T t r i) :=
          (congrArg SimpleGraph.Walk.support hpq).trans (SimpleGraph.Walk.support_map _ _)
        rw [hsupp, List.mem_map] at hs'
        obtain ⟨c, hc, rfl⟩ := hs'
        have key := (hX i).2.2.2 a c b q hq hc
        intro v hv
        simp only [X', Finset.mem_inter, Finset.mem_map, Function.Embedding.coe_subtype] at hv
        obtain ⟨⟨u, hu, rfl⟩, ⟨u', hu', huu'⟩⟩ := hv
        have : u' = u := Subtype.ext huu'
        subst this
        have := key (Finset.mem_inter.2 ⟨hu, hu'⟩)
        exact Finset.mem_map.2 ⟨_, this, rfl⟩
      · intro v hv
        simp only [X', Finset.mem_inter, Finset.mem_map, Function.Embedding.coe_subtype] at hv
        obtain ⟨⟨u, _, rfl⟩, ⟨u', _, huu'⟩⟩ := hv
        exfalso
        have h1 := u.2
        have h2 := u'.2
        rw [huu'] at h2
        exact Finset.disjoint_left.1 (hdisjoint i j hij) h1 h2
  · rintro (_ | ⟨i, a⟩)
    · simp [X']
    · simp only [X', Finset.card_map]
      exact hcard i a
