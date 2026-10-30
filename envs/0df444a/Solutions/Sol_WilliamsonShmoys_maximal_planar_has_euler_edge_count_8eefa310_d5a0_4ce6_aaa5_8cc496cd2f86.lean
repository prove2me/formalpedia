-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_has_euler_edge_count_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:30:15.440048+00:00
-- url     : https://prove2.me/submissions/f45f812c-8107-47ac-ad95-031c62857338

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
import Theorems.Thm_WilliamsonShmoys_planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
      J hV hJ
  have hnotlt : ¬ J.edgeSet.ncard < 3 * Fintype.card V - 6 := by
    intro hlt
    obtain ⟨K, hJK, hKplanar, hKneJ⟩ :=
      WilliamsonShmoys.planar_strict_supergraph_below_triangulation_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
        J hV hJ hlt
    have hKJ := hmax K hJK hKplanar
    exact hKneJ hKJ
  exact Nat.le_antisymm hupper (Nat.le_of_not_gt hnotlt)
