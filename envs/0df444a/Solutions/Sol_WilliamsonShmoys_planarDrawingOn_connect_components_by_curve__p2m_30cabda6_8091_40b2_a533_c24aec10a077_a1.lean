-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:30.945591+00:00
-- url     : https://prove2.me/submissions/e634774c-6624-4618-a578-e5155c2c9aa7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_disconnected_path__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) (G : SimpleGraph V)
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
    (hG_not_connected : ¬ G.Connected) :
    ∃ u v, u < v ∧ ¬ G.Adj u v ∧ ∃ γ : ℝ → ℝ × ℝ,
      ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧
      γ 0 = p u ∧ γ 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, γ t ≠ arc x y s) := by
  obtain ⟨u, v, huv, hnotReachable, γ, hcont, hzero, hone, hvertices, hedges⟩ :=
    WilliamsonShmoys.planarDrawingOn_disconnected_path__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
      hV G p arc hp hEdge hCross hG_not_connected
  have hnotAdj : ¬ G.Adj u v := fun hadj => hnotReachable hadj.reachable
  obtain ⟨γ', hcont', hinj, hzero', hone', hvertices', hedges'⟩ :=
    WilliamsonShmoys.planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
      G p arc hp huv γ hcont hzero hone hvertices hedges
  exact ⟨u, v, huv, hnotAdj, γ', hcont', hinj, hzero', hone', hvertices', hedges'⟩