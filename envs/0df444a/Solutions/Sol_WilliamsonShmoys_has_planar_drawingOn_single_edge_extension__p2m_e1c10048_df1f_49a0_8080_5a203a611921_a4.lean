-- Prove2me | solution 1 for WilliamsonShmoys.has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:23.313884+00:00
-- url     : https://prove2.me/submissions/fefdafb0-17b5-43d6-883c-f93d5a0d4939

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hAdj : ∀ a b, a < b →
      (K.Adj a b ↔ H.Adj a b ∨ (a = u ∧ b = v))) :
    HasPlanarDrawingOn K := by
  classical
  let newArc : V → V → ℝ → ℝ × ℝ := fun a b t =>
    if a = u ∧ b = v then c t else arc a b t
  refine ⟨p, newArc, hp, ?_, ?_⟩
  · intro a b hab hKab
    by_cases hs : a = u ∧ b = v
    · simpa [newArc, hs.1, hs.2] using
        (show ContinuousOn c (Set.Icc 0 1) ∧
          Set.InjOn c (Set.Icc 0 1) ∧ c 0 = p u ∧ c 1 = p v ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) from
            ⟨hccont, hcinj, hc0, hc1, hcvertices⟩)
    · have hHa : H.Adj a b := by
        rcases (hAdj a b hab).mp hKab with hHa | ⟨hau, hbv⟩
        · exact hHa
        · exact False.elim (hs ⟨hau, hbv⟩)
      simpa [newArc, hs] using hEdges a b hab hHa
  · intro a b x y hab hxy hKab hKxy hpairs t ht s hs heq
    by_cases hsa : a = u ∧ b = v
    · have hHx : H.Adj x y := by
        rcases (hAdj x y hxy).mp hKxy with hHx | ⟨hxu, hyv⟩
        · exact hHx
        · exact False.elim (hpairs (by rw [hsa.1, hsa.2, hxu, hyv]))
      have hsx : ¬ (x = u ∧ y = v) := by
        intro hx
        apply hpairs
        rcases hsa with ⟨rfl, rfl⟩
        rcases hx with ⟨rfl, rfl⟩
        rfl
      have hne : (u, v) ≠ (x, y) := by
        intro he
        apply hpairs
        simpa [hsa.1, hsa.2] using he
      have hresult := hccross x y hxy hHx hne t ht s hs
        (by simpa [newArc, hsa, hsx] using heq)
      exact hresult
    · by_cases hsx : x = u ∧ y = v
      · have hHa : H.Adj a b := by
          rcases (hAdj a b hab).mp hKab with hHa | ⟨hau, hbv⟩
          · exact hHa
          · exact False.elim (hsa ⟨hau, hbv⟩)
        have hne : (u, v) ≠ (a, b) := by
          intro he
          apply hpairs
          simpa [hsx.1, hsx.2] using he.symm
        have hresult := hccross a b hab hHa hne s hs t ht
          (by simpa [newArc, hsa, hsx] using heq.symm)
        exact ⟨hresult.2, hresult.1⟩
      · have hHa : H.Adj a b := by
          rcases (hAdj a b hab).mp hKab with hHa | ⟨hau, hbv⟩
          · exact hHa
          · exact False.elim (hsa ⟨hau, hbv⟩)
        have hHx : H.Adj x y := by
          rcases (hAdj x y hxy).mp hKxy with hHx | ⟨hxu, hyv⟩
          · exact hHx
          · exact False.elim (hsx ⟨hxu, hyv⟩)
        have hArc : arc a b t = arc x y s := by
          simpa [newArc, hsa, hsx] using heq
        exact hCross a b x y hab hxy hHa hHx hpairs t ht s hs hArc