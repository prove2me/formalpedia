-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:20.774863+00:00
-- url     : https://prove2.me/submissions/9dd997c1-1bc8-42fd-bdc8-2909f8dda9d0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hS : S.Nonempty := ⟨H, le_rfl, hDraw⟩
  obtain ⟨K, hK, hmax⟩ := WilliamsonShmoys.exists_maximal_graph_in_set__p2m_adb7eae7_2a82_406a_9d69_125f3f83074d_a1 S hS
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hLDraw
  apply hmax L ?_ hKL
  exact ⟨le_trans hK.1 hKL, hLDraw⟩