-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:52:24.437941+00:00
-- url     : https://prove2.me/submissions/b3b9613b-b743-480d-b4b9-61db5cdfe164
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨K, hHK, hK, htri⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_83d9f0a5_b086_4e9a_82e5_51c146823d01_a1
      H hcard hH
  have hEq : K = H := hmax K hHK hK
  subst K
  exact le_of_eq htri