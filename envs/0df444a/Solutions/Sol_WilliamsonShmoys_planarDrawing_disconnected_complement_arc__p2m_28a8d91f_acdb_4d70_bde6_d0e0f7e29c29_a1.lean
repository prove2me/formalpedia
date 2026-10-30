-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_disconnected_complement_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:30.501848+00:00
-- url     : https://prove2.me/submissions/9ea8e7cc-a339-4095-a77d-1aff9dde1a5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_unreachable_pair_avoiding_arc__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p ∧
      (∀ u v, u < v → H.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧ arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, ∃ gamma : ℝ → ℝ × ℝ,
      u < v ∧ ¬ H.Adj u v ∧
      ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) := by
  obtain ⟨u, v, huv, hnotAdj, hnotReachable⟩ :=
    WilliamsonShmoys.exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
      H hV hDisconnected
  obtain ⟨gamma, hcont, hinj, hstart, hend, hvertices, hedges⟩ :=
    WilliamsonShmoys.planarDrawing_unreachable_pair_avoiding_arc__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
      H p arc hp u v huv hnotAdj hnotReachable
  exact ⟨u, v, gamma, huv, hnotAdj, hcont, hinj, hstart, hend, hvertices, hedges⟩