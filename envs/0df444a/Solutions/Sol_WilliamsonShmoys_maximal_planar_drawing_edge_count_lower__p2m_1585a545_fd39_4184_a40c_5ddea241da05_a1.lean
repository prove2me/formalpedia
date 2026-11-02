-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:19.172397+00:00
-- url     : https://prove2.me/submissions/45db443b-0cc8-483a-a040-92d919e90235
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
import Theorems.Thm_WilliamsonShmoys_edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K → K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V ≤ M.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  obtain ⟨K, hMK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
      M hM hV
  have hKM : K ≤ M := hMax K hMK hK
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hcards :=
    WilliamsonShmoys.edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
      M K hMK hKM
  omega