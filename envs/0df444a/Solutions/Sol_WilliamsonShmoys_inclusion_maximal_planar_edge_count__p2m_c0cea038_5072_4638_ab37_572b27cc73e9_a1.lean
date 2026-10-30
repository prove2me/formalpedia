-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:34:28.91185+00:00
-- url     : https://prove2.me/submissions/e8d2e006-68b5-4877-bb27-c9ca234abd2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hPlanarN, hCount⟩ :=
    WilliamsonShmoys.exists_triangulated_extension__p2m_57ba8428_9b4f_42ca_9cfe_16138e676737_a2
      M hCard hM
  have hNM : N ≤ M := hMax N hMN hPlanarN
  have hGraph : N = M := le_antisymm hNM hMN
  have hEdges : N.edgeSet.ncard = M.edgeSet.ncard :=
    congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hGraph
  omega