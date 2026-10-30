-- Prove2me | solution 1 for WilliamsonShmoys.completion_maximal_drawable_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:50:26.716865+00:00
-- url     : https://prove2.me/submissions/1c6d9dcf-674c-48dc-9142-da5cc3bd1a73

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_augmentation_below_edge_bound

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  by_contra hnot
  have hlt : M.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨N, hMN, hNM, hdrawN⟩ :=
    WilliamsonShmoys.drawable_augmentation_below_edge_bound M hV hdraw hlt
  exact hNM (hmax N hMN hdrawN)