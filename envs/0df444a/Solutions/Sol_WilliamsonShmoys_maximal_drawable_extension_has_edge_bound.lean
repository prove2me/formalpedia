-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_has_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:48:41.794673+00:00
-- url     : https://prove2.me/submissions/add43449-83ad-4421-9e70-64f5b25d9864

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_edge_bound_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_augmentation_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.maximal_drawable_extension_edge_bound_20261026 L hL hV
  have hlower : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
    by_contra hnot
    have hlt : L.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
    obtain ⟨M, hLM, hM⟩ :=
      WilliamsonShmoys.maximal_drawable_extension_augmentation_20261026
        L hL hV hlt
    have hML : M = L := hmax M (le_of_lt hLM) hM
    rw [hML] at hLM
    exact (lt_irrefl L) hLM
  exact Nat.le_antisymm hupper hlower