-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:42:34.254375+00:00
-- url     : https://prove2.me/submissions/9e0dba80-63a5-4314-b4ff-3c66a8fd4570

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

open SimpleGraph

/-- Sufficient condition for the path axiom (iii): bags containing a vertex are
walk-connected inside a tree. -/
theorem taTD_iii_of_walks {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.IsAcyclic)
    (X : T → Finset V)
    (h : ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c) :
    ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s' := by
  classical
  intro s s' s'' p hp hs' v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨w, hw⟩ := h v s s'' hv.1 hv.2
  have heq : (⟨w.bypass, w.bypass_isPath⟩ : t.Path s s'') = ⟨p, hp⟩ :=
    (ht.subsingleton_path s s'').elim _ _
  have hq : w.bypass = p := congrArg Subtype.val heq
  apply hw
  apply w.support_bypass_subset_support
  rw [hq]; exact hs'

theorem taTD_walks_of_iii {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.Connected)
    (X : T → Finset V)
    (h : ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s') :
    ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c := by
  classical
  intro v a b ha hb
  obtain ⟨w⟩ := ht.preconnected a b
  refine ⟨w.bypass, fun c hc => ?_⟩
  exact h a c b w.bypass w.bypass_isPath hc (Finset.mem_inter.2 ⟨ha, hb⟩)

section Leaves
variable {T : Type} (t : SimpleGraph T) {m : ℕ} (sj : Fin m → T)

/-- The tree with one leaf `inr j` attached to `inl (sj j)` for each `j`. -/
def leafTree : SimpleGraph (T ⊕ Fin m) :=
  (t ⊕g (⊥ : SimpleGraph (Fin m))) ⊔ fromEdgeSet (Set.range fun j => s(Sum.inl (sj j), Sum.inr j))

theorem leafTree_adj_inl_inl (a b : T) : (leafTree t sj).Adj (Sum.inl a) (Sum.inl b) ↔ t.Adj a b := by
  simp [leafTree]

theorem leafTree_adj_inl_inr (j : Fin m) : (leafTree t sj).Adj (Sum.inl (sj j)) (Sum.inr j) := by
  simp [leafTree]

theorem leafTree_adj_inr_inl (j : Fin m) : (leafTree t sj).Adj (Sum.inr j) (Sum.inl (sj j)) :=
  (leafTree_adj_inl_inr t sj j).symm

/-- The embedding of `t` into the leaf tree. -/
def leafHom : t →g leafTree t sj where
  toFun := Sum.inl
  map_rel' := fun h => (leafTree_adj_inl_inl t sj _ _).2 h

/-- Lifting a walk of `t` to the leaf tree. -/
def liftWalk : ∀ {a b : T}, t.Walk a b → (leafTree t sj).Walk (Sum.inl a) (Sum.inl b)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons ((leafTree_adj_inl_inl t sj _ _).2 h) (liftWalk p)

theorem liftWalk_support : ∀ {a b : T} (w : t.Walk a b) (c : T ⊕ Fin m),
    c ∈ (liftWalk t sj w).support → ∃ c0 ∈ w.support, c = Sum.inl c0
  | _, _, .nil, c, hc => by
    simp [liftWalk] at hc
    exact ⟨_, by simp, hc⟩
  | _, _, .cons h p, c, hc => by
    simp only [liftWalk, Walk.support_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨_, by simp, hc⟩
    · obtain ⟨c0, hc0, rfl⟩ := liftWalk_support p c hc
      exact ⟨c0, by simp [hc0], rfl⟩

theorem leafTree_connected (ht : t.Connected) : (leafTree t sj).Connected := by
  have hinl : ∀ a b : T, (leafTree t sj).Reachable (Sum.inl a) (Sum.inl b) := by
    intro a b
    obtain ⟨w⟩ := ht.preconnected a b
    exact ⟨w.map (leafHom t sj)⟩
  have hall : ∀ x : T ⊕ Fin m, ∃ a, (leafTree t sj).Reachable x (Sum.inl a) := by
    intro x
    cases x with
    | inl a => exact ⟨a, Reachable.refl _⟩
    | inr j => exact ⟨sj j, (leafTree_adj_inr_inl t sj j).reachable⟩
  have : Nonempty T := ht.nonempty
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hall x
  obtain ⟨b, hb⟩ := hall y
  exact ha.trans ((hinl a b).trans hb.symm)

theorem leafTree_isTree [Finite T] (ht : t.IsTree) : (leafTree t sj).IsTree := by
  classical
  have hT := (isTree_iff_connected_and_card.1 ht).2
  rw [isTree_iff_connected_and_card]
  refine ⟨leafTree_connected t sj ht.connected, ?_⟩
  have hfinE : (t.edgeSet).Finite := Set.toFinite _
  have h1 : Nat.card ((t ⊕g (⊥ : SimpleGraph (Fin m))).edgeSet) = Nat.card t.edgeSet := by
    rw [Nat.card_congr (edgeSetSumEquiv), Nat.card_sum]
    simp
  have hL : (fromEdgeSet (Set.range fun j : Fin m => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ Fin m)))).edgeSet
      = Set.range fun j : Fin m => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ Fin m)) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨j, rfl⟩ := h
      simp
  have hinj : Function.Injective fun j : Fin m => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ Fin m)) := by
    intro j k hjk
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at hjk
    rcases hjk with ⟨_, h⟩ | h
    · exact h
    · simp at h
  have hdisj : Disjoint (t ⊕g (⊥ : SimpleGraph (Fin m))).edgeSet
      (Set.range fun j : Fin m => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ Fin m))) := by
    rw [Set.disjoint_left]
    rintro e he ⟨j, rfl⟩
    simp at he
  have hfin1 : ((t ⊕g (⊥ : SimpleGraph (Fin m))).edgeSet).Finite := Set.toFinite _
  have hfin2 : (Set.range fun j : Fin m => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ Fin m))).Finite :=
    Set.finite_range _
  rw [Nat.card_coe_set_eq, leafTree, edgeSet_sup, hL, Set.ncard_union_eq hdisj hfin1 hfin2,
    Set.ncard_range_of_injective hinj, ← Nat.card_coe_set_eq, h1, Nat.card_sum, ← hT]
  simp
  ring

end Leaves

theorem ta_prop3 (I : Instance) (hI : I.Standing) (ω : ℕ)
    (hω : HypTreewidthLE I ω) :
    RobertsonSeymour1986.GM5.TreewidthLE (auxGraph I) (ω + 1) := by
  classical
  obtain ⟨T, hfT, t, X, hTD, hcov, hw⟩ := hω
  obtain ⟨htree, hvert, hedge, hpath⟩ := hTD
  choose sj hsj using hcov
  let X' : T ⊕ Fin I.m → Finset (Fin I.n ⊕ Fin I.m) := fun x =>
    match x with
    | Sum.inl a => (X a).map ⟨Sum.inl, Sum.inl_injective⟩
    | Sum.inr j => (I.e j).map ⟨Sum.inl, Sum.inl_injective⟩ ∪ {Sum.inr j}
  have hX'l : ∀ a v, v ∈ X' (Sum.inl a) ↔ ∃ i, v = Sum.inl i ∧ i ∈ X a := by
    intro a v
    cases v with
    | inl i => simp [X']
    | inr j => simp [X']
  have hX'r : ∀ j v, v ∈ X' (Sum.inr j) ↔ (∃ i, v = Sum.inl i ∧ i ∈ I.e j) ∨ v = Sum.inr j := by
    intro j v
    cases v with
    | inl i => simp [X']
    | inr k => simp [X']
  have hwalks := taTD_walks_of_iii htree.connected X hpath
  refine ⟨T ⊕ Fin I.m, inferInstance, leafTree t sj, X', ⟨leafTree_isTree t sj htree, ?_, ?_, ?_⟩, ?_⟩
  · -- every vertex is covered
    intro v
    cases v with
    | inl i =>
      obtain ⟨s, hs⟩ := hvert i
      exact ⟨Sum.inl s, (hX'l s _).2 ⟨i, rfl, hs⟩⟩
    | inr j => exact ⟨Sum.inr j, (hX'r j _).2 (Or.inr rfl)⟩
  · -- every edge is covered
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl k => exact absurd hxy (by simp [auxGraph])
      | inr j =>
        have : i ∈ I.e j := by simpa [auxGraph] using hxy
        exact ⟨Sum.inr j, (hX'r j _).2 (Or.inl ⟨i, rfl, this⟩), (hX'r j _).2 (Or.inr rfl)⟩
    | inr j =>
      cases y with
      | inl i =>
        have : i ∈ I.e j := by simpa [auxGraph] using hxy
        exact ⟨Sum.inr j, (hX'r j _).2 (Or.inr rfl), (hX'r j _).2 (Or.inl ⟨i, rfl, this⟩)⟩
      | inr k => exact absurd hxy (by simp [auxGraph])
  · -- path axiom, via walk-connectivity of the bags containing a vertex
    apply taTD_iii_of_walks (leafTree_isTree t sj htree).isAcyclic X'
    intro v a b ha hb
    cases v with
    | inr j =>
      -- only the leaf `inr j` contains `inr j`
      have honly : ∀ x, Sum.inr j ∈ X' x → x = Sum.inr j := by
        intro x hx
        cases x with
        | inl a => obtain ⟨i, hi, _⟩ := (hX'l a _).1 hx; cases hi
        | inr k =>
          rcases (hX'r k _).1 hx with ⟨i, hi, _⟩ | hk
          · cases hi
          · cases hk; rfl
      have ha' := honly a ha
      have hb' := honly b hb
      subst ha' hb'
      exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ha⟩
    | inl i =>
      -- go from each endpoint to an original node containing `i`
      have hhome : ∀ x, Sum.inl i ∈ X' x → ∃ (a0 : T) (w : (leafTree t sj).Walk x (Sum.inl a0)),
          i ∈ X a0 ∧ ∀ c ∈ w.support, Sum.inl i ∈ X' c := by
        intro x hx
        cases x with
        | inl a =>
          obtain ⟨i', hi', hia⟩ := (hX'l a _).1 hx
          cases hi'
          exact ⟨a, Walk.nil, hia, fun c hc => by simp at hc; subst hc; exact hx⟩
        | inr j =>
          rcases (hX'r j _).1 hx with ⟨i', hi', hie⟩ | hk
          · cases hi'
            have hia : i ∈ X (sj j) := hsj j hie
            refine ⟨sj j, Walk.cons (leafTree_adj_inr_inl t sj j) Walk.nil, hia, ?_⟩
            intro c hc
            simp at hc
            rcases hc with rfl | rfl
            · exact hx
            · exact (hX'l _ _).2 ⟨i, rfl, hia⟩
          · cases hk
      obtain ⟨a0, wa, hia, hwa⟩ := hhome a ha
      obtain ⟨b0, wb, hib, hwb⟩ := hhome b hb
      obtain ⟨w, hw⟩ := hwalks i a0 b0 hia hib
      refine ⟨wa.append ((liftWalk t sj w).append wb.reverse), ?_⟩
      intro c hc
      rcases (Walk.mem_support_append_iff _ _).1 hc with hc | hc
      swap
      rcases (Walk.mem_support_append_iff _ _).1 hc with hc | hc
      rotate_left
      rotate_left
      · exact hwa c hc
      · obtain ⟨c0, hc0, rfl⟩ := liftWalk_support t sj w c hc
        exact (hX'l _ _).2 ⟨i, rfl, hw c0 hc0⟩
      · rw [Walk.support_reverse, List.mem_reverse] at hc
        exact hwb c hc
  · -- width
    intro x
    cases x with
    | inl a =>
      have := hw a
      simp only [X', Finset.card_map]
      omega
    | inr j =>
      have h1 := Finset.card_le_card (hsj j)
      have h2 := hw (sj j)
      simp only [X']
      refine le_trans (Finset.card_union_le _ _) ?_
      simp only [Finset.card_map, Finset.card_singleton]
      omega

end TraceAdopt.LPReform

open TraceAdopt.LPReform in
theorem solution (I : Instance) (hI : I.Standing) (ω : ℕ)
    (hω : HypTreewidthLE I ω) :
    RobertsonSeymour1986.GM5.TreewidthLE (auxGraph I) (ω + 1) :=
  ta_prop3 I hI ω hω
