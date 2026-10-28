-- Prove2me | solution 2 for WilliamsonShmoys.planar_augmentation_from_connector_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:43:54.903718+00:00
-- url     : https://prove2.me/submissions/404036e4-a8ca-472d-b332-881b4592a45d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem S181core {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (u v : V) (huv : u < v) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (γ : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (h1 : ∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧ Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (h2 : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (g1 : ContinuousOn γ (Set.Icc 0 1)) (g2 : Set.InjOn γ (Set.Icc 0 1))
    (g3 : γ 0 = p u) (g4 : γ 1 = p v) (g5 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (g6 : ∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hOnly : ∀ x y, H.Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  have key : ∀ x y, x < y → H.Adj x y →
      (x = u ∧ y = v) ∨ (¬ (x = u ∧ y = v) ∧ G.Adj x y) := by
    intro x y hxy hH
    by_cases h : x = u ∧ y = v
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rcases hOnly x y hH with h' | h' | ⟨rfl, rfl⟩
      · exact h'
      · exact (h h').elim
      · exact (lt_asymm hxy huv).elim
  refine ⟨p, fun x y => if x = u ∧ y = v then γ else arc x y, hp,
    fun x y hxy hH => ?_, fun x y a b hxy hab hH1 hH2 hne t ht s hs heq => ?_⟩
  · rcases key x y hxy hH with h | ⟨hn, hG⟩
    · simp only [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨g1, g2, g3, g4, g5⟩
    · simp only [if_neg hn]
      exact h1 x y hxy hG
  · rcases key x y hxy hH1 with h | ⟨hn, hG⟩ <;> rcases key a b hab hH2 with h' | ⟨hn', hG'⟩
    · exact (hne (by rw [h.1, h.2, h'.1, h'.2])).elim
    · simp only [if_pos h, if_neg hn'] at heq
      exact g6 a b hab hG' t ht s hs heq
    · simp only [if_pos h', if_neg hn] at heq
      exact (g6 x y hxy hG s hs t ht heq.symm).symm
    · simp only [if_neg hn, if_neg hn'] at heq
      exact h2 x y a b hxy hab hG hG' hne t ht s hs heq

theorem S181conn {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v)
    (hgeom : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (c : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧ Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (ContinuousOn c (Set.Icc 0 1) ∧ Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p (min u v) ∧ c 1 = p (max u v) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, c t = arc x y s →
            ∃ w, (w = min u v ∨ w = max u v) ∧ (w = x ∨ w = y) ∧
              ((t = 0 ∧ w = min u v) ∨ (t = 1 ∧ w = max u v)) ∧
              ((s = 0 ∧ w = x) ∨ (s = 1 ∧ w = y))))) :
    WilliamsonShmoys.HasPlanarDrawingOn
      (SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet)) := by
  obtain ⟨p, arc, c, hp, h1, h2, g1, g2, g3, g4, g5, g6⟩ := hgeom
  have hne : u ≠ v := fun h => hdisconnected (by subst h; exact Relation.ReflTransGen.refl)
  have hlt : min u v < max u v := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  refine S181core H _ (min u v) (max u v) hlt p arc c hp h1 h2 g1 g2 g3 g4 g5
    (fun x y hxy hH t ht s hs he => ?_) (fun x y hK => ?_)
  · obtain ⟨w, -, -, ht', hs'⟩ := g6 x y hxy hH t ht s hs he
    exact ⟨ht'.imp And.left And.left, hs'.imp And.left And.left⟩
  · rw [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Sym2.eq_iff] at hK
    obtain ⟨h | h, -⟩ := hK
    · right
      rcases le_total u v with h' | h'
      · rw [min_eq_left h', max_eq_right h']; tauto
      · rw [min_eq_right h', max_eq_left h']; tauto
    · left; exact h

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v)
    (hgeom : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (c : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (ContinuousOn c (Set.Icc 0 1) ∧
        Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p (min u v) ∧ c 1 = p (max u v) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            c t = arc x y s →
              ∃ w, (w = min u v ∨ w = max u v) ∧ (w = x ∨ w = y) ∧
                ((t = 0 ∧ w = min u v) ∨ (t = 1 ∧ w = max u v)) ∧
                ((s = 0 ∧ w = x) ∨ (s = 1 ∧ w = y))))) :
    ∃ K : SimpleGraph V,
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  have hne : u ≠ v := fun h => hdisconnected (by subst h; exact Relation.ReflTransGen.refl)
  refine ⟨SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet), fun x y h => ?_, ⟨s(u, v), ?_, ?_⟩,
    ?_, S181conn H u v hdisconnected hgeom⟩
  · rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_insert_of_mem _ h, H.ne_of_adj h⟩
  · intro h
    exact hdisconnected (Relation.ReflTransGen.single h)
  · rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rcases h with rfl | h
    · simpa using hne
    · exact H.not_isDiag_of_mem_edgeSet h
  · rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_insert _ _, hne⟩
