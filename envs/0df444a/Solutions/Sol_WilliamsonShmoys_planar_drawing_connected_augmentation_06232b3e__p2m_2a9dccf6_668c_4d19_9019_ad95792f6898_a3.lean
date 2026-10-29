-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:36:44.543374+00:00
-- url     : https://prove2.me/submissions/48bfe77f-5382-4610-a8af-f895827090fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_component_edge_extension__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
import Theorems.Thm_WilliamsonShmoys_finite_planar_connected_completion__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hLK, hConn, hK⟩ :=
    WilliamsonShmoys.finite_planar_connected_completion__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
      L hL hCard (by
        intro H hLH hH u v huv hdis
        exact WilliamsonShmoys.planar_component_edge_extension__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
          H hH huv hdis)
  refine ⟨K, hLK, hConn, hK, ?_⟩
  apply Set.ncard_mono
  exact SimpleGraph.edgeSet_subset_edgeSet.mpr hLK