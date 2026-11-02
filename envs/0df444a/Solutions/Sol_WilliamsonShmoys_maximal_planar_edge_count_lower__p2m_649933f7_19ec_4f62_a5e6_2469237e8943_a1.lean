-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:57.732616+00:00
-- url     : https://prove2.me/submissions/24c66c7e-cd15-4663-a302-05bcd02f4727
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M)
    : letI : DecidableRel M.Adj := dM
      6 * Fintype.card V ≤ 2 * M.edgeFinset.card + 12 := by
  classical
  letI : DecidableRel M.Adj := dM
  obtain ⟨N, dN, hMN, hNdraw, hNcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
      M hM hcard
  letI : DecidableRel N.Adj := dN
  have hNM : N ≤ M := hmax N hMN hNdraw
  have hMNcard : M.edgeFinset.card ≤ N.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hMN)
  have hNMcard : N.edgeFinset.card ≤ M.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hNM)
  have hcardEq : N.edgeFinset.card = M.edgeFinset.card :=
    Nat.le_antisymm hNMcard hMNcard
  omega