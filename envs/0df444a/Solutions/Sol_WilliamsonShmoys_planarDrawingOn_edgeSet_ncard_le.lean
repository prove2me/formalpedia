-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:20:29.999399+00:00
-- url     : https://prove2.me/submissions/bc70d48f-4f13-4026-96ec-aa6aa1ba4f74

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_planar_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hNcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_exists_maximal_planar_supergraph M hV hM
  calc
    M.edgeSet.ncard ≤ N.edgeSet.ncard := Set.ncard_mono hMN
    _ = 3 * Fintype.card V - 6 := hNcard
