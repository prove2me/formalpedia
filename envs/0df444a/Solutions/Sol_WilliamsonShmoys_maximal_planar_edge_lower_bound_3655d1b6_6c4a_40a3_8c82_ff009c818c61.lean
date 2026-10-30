-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_3655d1b6_6c4a_40a3_8c82_ff009c818c61
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:21:28.239581+00:00
-- url     : https://prove2.me/submissions/89738d0e-c638-424d-86ab-c70139ded9f1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation_edge_count

set_option autoImplicit false

/-- The maximality hypothesis identifies the given graph with the triangulated
supergraph supplied by the planar augmentation theorem. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_augmentation_edge_count K hV hK
  rw [hmax L hKL hL] at hcount
  omega