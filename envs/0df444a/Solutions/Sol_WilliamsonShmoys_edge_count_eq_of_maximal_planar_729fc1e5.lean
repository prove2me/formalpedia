-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_maximal_planar_729fc1e5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:11:52.740184+00:00
-- url     : https://prove2.me/submissions/3a2f4c48-d457-41b0-82cb-4b9dfe932b6f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_729fc1e5
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_729fc1e5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound_729fc1e5 R hV hR
  by_contra hne
  have hlt : R.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨S, hRS, hSR, hS⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_729fc1e5 R hV hR hlt
  exact hSR (hmax S hRS hS)