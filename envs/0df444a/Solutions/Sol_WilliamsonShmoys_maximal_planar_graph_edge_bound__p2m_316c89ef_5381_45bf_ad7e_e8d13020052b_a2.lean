-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:37.655021+00:00
-- url     : https://prove2.me/submissions/dd96d8a1-e151-47e2-b193-36cc64e094a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (_ : DecidableRel L.Adj),
      3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by
  classical
  obtain ⟨M, hLM, hMplanar, dM, hMcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
      L hL hcard
  letI : DecidableRel M.Adj := dM
  have hML : M ≤ L := hmax M hLM hMplanar
  have hEq : M = L := le_antisymm hML hLM
  subst M
  exact ⟨inferInstance, by omega⟩