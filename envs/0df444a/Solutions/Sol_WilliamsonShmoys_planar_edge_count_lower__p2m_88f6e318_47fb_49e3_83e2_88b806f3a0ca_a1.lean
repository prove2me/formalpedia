-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:01:44.428773+00:00
-- url     : https://prove2.me/submissions/7c3948da-5436-43c7-b881-e3b0c2ac48e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     3 * Fintype.card V <= H.edgeFinset.card + 6) := by
  classical
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
      H hV hH
  have hKH : K = H := hmax K hHK hK
  subst K
  exact hcount.le