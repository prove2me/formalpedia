-- Prove2me | solution 1 for WilliamsonShmoys.extended_drawing_data_from_clean_arc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:56:42.369712+00:00
-- url     : https://prove2.me/submissions/58a5e877-4fc1-43ec-b424-d9b318900128

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arc x y) (Set.Icc 0 1) ∧
      Set.InjOn (arc x y) (Set.Icc 0 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hCross : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
      (x, y) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc x y t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hγContinuous : ContinuousOn γ (Set.Icc 0 1))
    (hγInjective : Set.InjOn γ (Set.Icc 0 1))
    (hγStart : γ 0 = p u)
    (hγEnd : γ 1 = p v)
    (hγAvoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγCross : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ arcNew : V → V → ℝ → ℝ × ℝ,
      (∀ x y, x < y →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj x y →
        ContinuousOn (arcNew x y) (Set.Icc 0 1) ∧
        Set.InjOn (arcNew x y) (Set.Icc 0 1) ∧
        arcNew x y 0 = p x ∧ arcNew x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arcNew x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj x y →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arcNew x y t = arcNew a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  classical
  let arcNew : V → V → ℝ → ℝ × ℝ :=
    fun x y t => if x = u ∧ y = v then γ t else arc x y t
  have adjClass : ∀ {x y : V}, x < y →
      (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) := by
    intro x y hxy hadj
    change G.Adj x y ∨ (x ≠ y ∧
      ((x = u ∧ y = v) ∨ (y = u ∧ x = v))) at hadj
    rcases hadj with hG | ⟨_, hnew⟩
    · exact Or.inl hG
    · rcases hnew with hnew | hrev
      · exact Or.inr hnew
      · rcases hrev with ⟨hyu, hxv⟩
        have hvu : v < u := by simpa [hxv, hyu] using hxy
        exact (lt_asymm huv hvu).elim
  refine ⟨arcNew, ?_, ?_⟩
  · intro x y hxy hadj
    by_cases hnew : x = u ∧ y = v
    · rcases hnew with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [arcNew] using hγContinuous
      · simpa [arcNew] using hγInjective
      · simpa [arcNew] using hγStart
      · simpa [arcNew] using hγEnd
      · intro t ht w
        simpa [arcNew] using hγAvoid t ht w
    · have hc := adjClass hxy hadj
      rcases hc with hG | hbad
      · have hprop := hEdges x y hxy hG
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa [arcNew, hnew] using hprop.1
        · intro t ht s hs hEq
          apply hprop.2.1 ht hs
          simpa [arcNew, hnew] using hEq
        · simpa [arcNew, hnew] using hprop.2.2.1
        · simpa [arcNew, hnew] using hprop.2.2.2.1
        · intro t ht w
          simpa [arcNew, hnew] using hprop.2.2.2.2 t ht w
      · exact (hnew hbad).elim
  · intro x y a b hxy hab hxyAdj habAdj hneq t ht s hs hEq
    by_cases hxNew : x = u ∧ y = v
    · by_cases haNew : a = u ∧ b = v
      · apply False.elim
        apply hneq
        rcases hxNew with ⟨rfl, rfl⟩
        rcases haNew with ⟨rfl, rfl⟩
        rfl
      · have hc := adjClass hab habAdj
        have hGa : G.Adj a b := by
          rcases hc with hGa | hbad
          · exact hGa
          · exact (haNew hbad).elim
        have hprop := hγCross a b hab hGa t ht s hs
        simpa [arcNew, hxNew, haNew] using hprop
          (by simpa [arcNew, hxNew, haNew] using hEq)
    · by_cases haNew : a = u ∧ b = v
      · have hc := adjClass hxy hxyAdj
        have hGx : G.Adj x y := by
          rcases hc with hGx | hbad
          · exact hGx
          · exact (hxNew hbad).elim
        have hprop := hγCross x y hxy hGx s hs t ht
        have hEq' : γ s = arc x y t := by
          simpa [arcNew, hxNew, haNew] using hEq.symm
        have hres := hprop hEq'
        exact ⟨hres.2, hres.1⟩
      · have hcx := adjClass hxy hxyAdj
        have hca := adjClass hab habAdj
        have hGx : G.Adj x y := by
          rcases hcx with hGx | hbad
          · exact hGx
          · exact (hxNew hbad).elim
        have hGa : G.Adj a b := by
          rcases hca with hGa | hbad
          · exact hGa
          · exact (haNew hbad).elim
        have hprop := hCross x y a b hxy hab hGx hGa hneq t ht s hs
        apply hprop
        simpa [arcNew, hxNew, haNew] using hEq
