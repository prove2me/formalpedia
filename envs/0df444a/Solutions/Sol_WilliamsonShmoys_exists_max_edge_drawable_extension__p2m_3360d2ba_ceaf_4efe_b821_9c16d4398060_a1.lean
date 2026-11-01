-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_drawable_extension__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:29:24.832196+00:00
-- url     : https://prove2.me/submissions/f0ecc451-afd8-4060-bf0b-b6ca4b1a1c55

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
import Theorems.Thm_WilliamsonShmoys_exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L →
        Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤
          Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by
  classical
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_max_nat_on_finite_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
      (α := SimpleGraph V)
      (P := fun K => H ≤ K ∧ HasPlanarDrawingOn K)
      (f := fun K => Nat.card {e : Sym2 V // e ∈ K.edgeSet})
      ⟨H, le_rfl, hH⟩
  exact ⟨K, hK.1, hK.2, fun L hHL hL => hmax L ⟨hHL, hL⟩⟩
