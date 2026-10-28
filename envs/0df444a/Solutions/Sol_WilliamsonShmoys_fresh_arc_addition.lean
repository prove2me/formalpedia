-- Prove2me | solution 1 for WilliamsonShmoys.fresh_arc_addition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:58:35.032396+00:00
-- url     : https://prove2.me/submissions/51755337-473e-4028-931c-4f83b7a810c4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem fa_main
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u < v)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hbase : Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (γ : ℝ → ℝ × ℝ)
    (hγcont : ContinuousOn γ (Set.Icc 0 1))
    (hγinj : Set.InjOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = p u) (hγ1 : γ 1 = p v)
    (hγvert : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγedge : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t ≠ arc x y s)
    (hnew : ¬ G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by
  obtain ⟨hpinj, harc, hcross⟩ := hbase
  classical
  let arc' : V → V → ℝ → ℝ × ℝ := fun x y => if x = u ∧ y = v then γ else arc x y
  have hadj : ∀ x y, x < y → (G ⊔ SimpleGraph.edge u v).Adj x y →
      ¬ (x = u ∧ y = v) → G.Adj x y := by
    intro x y hxy h hne
    rcases h with h | h
    · exact h
    · rw [SimpleGraph.edge_adj] at h
      rcases h with ⟨h1 | h1, _⟩
      · exact absurd ⟨h1.1, h1.2⟩ hne
      · obtain ⟨rfl, rfl⟩ := h1
        exact absurd hxy (lt_asymm huv)
  -- endpoints of γ are not interior points of old arcs
  have hend : ∀ x y, x < y → G.Adj x y → ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      γ t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
    intro x y hxy hG t ht s hs heq
    have ht' : t = 0 ∨ t = 1 := by
      by_contra hc
      push_neg at hc
      exact hγedge x y hxy hG t ⟨lt_of_le_of_ne ht.1 (Ne.symm hc.1),
        lt_of_le_of_ne ht.2 hc.2⟩ s hs heq
    refine ⟨ht', ?_⟩
    by_contra hc
    push_neg at hc
    have hsI : s ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hc.1), lt_of_le_of_ne hs.2 hc.2⟩
    rcases ht' with rfl | rfl
    · exact (harc x y hxy hG).2.2.2.2 s hsI u (heq ▸ hγ0)
    · exact (harc x y hxy hG).2.2.2.2 s hsI v (heq ▸ hγ1)
  refine ⟨G ⊔ SimpleGraph.edge u v, le_sup_left, ⟨p, arc', hpinj, ?_, ?_⟩, ?_⟩
  · intro x y hxy h
    by_cases hc : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [arc', and_self, if_true]
      exact ⟨hγcont, hγinj, hγ0, hγ1, hγvert⟩
    · simp only [arc', hc, if_false]
      exact harc x y hxy (hadj x y hxy h hc)
  · intro x y a b hxy hab h1 h2 hne t ht s hs heq
    by_cases c1 : x = u ∧ y = v
    · have c2 : ¬ (a = u ∧ b = v) := by
        rintro ⟨rfl, rfl⟩; exact hne (by rw [c1.1, c1.2])
      simp only [arc', c1, c2, and_self, if_true, if_false] at heq
      exact hend a b hab (hadj a b hab h2 c2) t ht s hs heq
    · by_cases c2 : a = u ∧ b = v
      · simp only [arc', c1, c2, and_self, if_true, if_false] at heq
        exact (hend x y hxy (hadj x y hxy h1 c1) s hs t ht heq.symm).symm
      · simp only [arc', c1, c2, if_false] at heq
        exact hcross x y a b hxy hab (hadj x y hxy h1 c1) (hadj a b hab h2 c2) hne t ht s hs heq
  · right
    rw [SimpleGraph.edge_adj]
    exact ⟨Or.inl ⟨rfl, rfl⟩, huv.ne⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hbase : Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (γ : ℝ → ℝ × ℝ)
    (hγcont : ContinuousOn γ (Set.Icc 0 1))
    (hγinj : Set.InjOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = p u) (hγ1 : γ 1 = p v)
    (hγvert : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγedge : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t ≠ arc x y s)
    (hnew : ¬ G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Adj u v := by
  rcases lt_or_gt_of_ne huv with h | h
  · exact fa_main G u v h p arc hbase γ hγcont hγinj hγ0 hγ1 hγvert hγedge hnew
  · have hmaps : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨H, hGH, hH, hadj⟩ := fa_main G v u h p arc hbase (fun t => γ (1 - t))
      (hγcont.comp (by fun_prop) hmaps)
      (by
        intro a ha b hb hab
        have := hγinj (hmaps ha) (hmaps hb) hab
        simp only at this; linarith)
      (by simp [hγ1]) (by simp [hγ0])
      (by intro t ht w; exact hγvert (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ w)
      (by intro x y hxy hG t ht s hs
          exact hγedge x y hxy hG (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ s hs)
      (fun h' => hnew h'.symm)
    exact ⟨H, hGH, hH, hadj.symm⟩
