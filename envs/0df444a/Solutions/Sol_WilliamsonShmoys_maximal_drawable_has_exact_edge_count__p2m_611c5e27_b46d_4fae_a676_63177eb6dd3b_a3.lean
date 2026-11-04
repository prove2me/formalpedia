-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:57:31.552283+00:00
-- url     : https://prove2.me/submissions/08b79d67-2d59-4897-839d-71970ed7aca7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K)
    (hMaximal : forall H : SimpleGraph V, K <= H -> HasPlanarDrawingOn H -> H <= K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1 K hV hPlanar
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1 K hV hPlanar hMaximal
  omega