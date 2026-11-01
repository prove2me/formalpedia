-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_face_count__p2m_b3780c9f_7548_4d87_b8fb_1d68dbe20f67_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:57.5282+00:00
-- url     : https://prove2.me/submissions/7afa06da-4074-4060-9b90-6bfd8cbb82d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
      M hplanar hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
      M hplanar hmax hcard
  have hedge : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    Nat.le_antisymm hupper hlower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega