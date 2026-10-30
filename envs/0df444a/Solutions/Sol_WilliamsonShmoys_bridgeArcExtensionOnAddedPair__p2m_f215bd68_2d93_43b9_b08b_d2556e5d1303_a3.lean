-- Prove2me | solution 1 for WilliamsonShmoys.bridgeArcExtensionOnAddedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:58.984953+00:00
-- url     : https://prove2.me/submissions/2b256c6d-bc02-44f8-a3c0-18ebb98ed275

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v) (hreach : ¬ G.Reachable u v)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hcrossGamma : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
        gamma t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (H : SimpleGraph V)
    (hAdj : ∀ x y, H.Adj x y ↔
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ q : V → V → ℝ → ℝ × ℝ,
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ c d, c < d → H.Adj c d → (x, y) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, q x y t = arc x y t) := by
  have hnot : ¬ G.Adj u v := fun huvAdj => hreach (SimpleGraph.Adj.reachable huvAdj)
  have hedge : ∀ a b, a < b → H.Adj a b →
      G.Adj a b ∨ (a = u ∧ b = v) := by
    intro a b hab h
    rcases (hAdj a b).mp h with hG | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl hG
    · exact Or.inr ⟨ha, hb⟩
    · have hba : v < u := by simpa [ha, hb] using hab
      exact False.elim ((not_lt_of_ge huv.le) hba)
  let q : V → V → ℝ → ℝ × ℝ :=
    fun x y t => if x = u ∧ y = v then gamma t else arc x y t
  refine ⟨q, ?_, ?_⟩
  · intro x y hxy hH
    rcases hedge x y hxy hH with hG | hnew
    · have hsp : ¬ (x = u ∧ y = v) := by
        rintro ⟨rfl, rfl⟩
        exact hnot hG
      rcases hEdge x y hxy hG with ⟨hc, hi, h0, h1, hvtx⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [q, hsp] using hc
      · simpa [q, hsp] using hi
      · simpa [q, hsp] using h0
      · simpa [q, hsp] using h1
      · simpa [q, hsp] using hvtx
      · intro c d hcd hHcd hne t ht s hs heq
        rcases hedge c d hcd hHcd with hGcd | hnewcd
        · have hsc : ¬ (c = u ∧ d = v) := by
            rintro ⟨rfl, rfl⟩
            exact hnot hGcd
          have heq' : arc x y t = arc c d s := by
            simpa [q, hsp, hsc] using heq
          exact hCross x y c d hxy hcd hG hGcd hne t ht s hs heq'
        · have heq' : gamma s = arc x y t := by
            simpa [q, hsp, hnewcd] using heq.symm
          have hcros := hcrossGamma x y hxy hG s hs t ht heq'
          exact ⟨hcros.2, hcros.1⟩
    · rcases hnew with ⟨hx, hy⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [q, hx, hy] using hcont
      · simpa [q, hx, hy] using hinj
      · simpa [q, hx, hy] using hzero
      · simpa [q, hx, hy] using hone
      · simpa [q, hx, hy] using hvertex
      · intro c d hcd hHcd hne t ht s hs heq
        rcases hedge c d hcd hHcd with hGcd | hnewcd
        · have hsc : ¬ (c = u ∧ d = v) := by
            intro hcdNew
            apply hne
            exact Prod.ext (hx.trans hcdNew.1.symm) (hy.trans hcdNew.2.symm)
          have heq' : gamma t = arc c d s := by
            simpa [q, hx, hy, hsc] using heq
          exact hcrossGamma c d hcd hGcd t ht s hs heq'
        · rcases hnewcd with ⟨hc, hd⟩
          apply False.elim (hne ?_)
          exact Prod.ext (hx.trans hc.symm) (hy.trans hd.symm)
  · intro x y hxy hG t ht
    have hsp : ¬ (x = u ∧ y = v) := by
      rintro ⟨rfl, rfl⟩
      exact hnot hG
    simp [q, hsp]
