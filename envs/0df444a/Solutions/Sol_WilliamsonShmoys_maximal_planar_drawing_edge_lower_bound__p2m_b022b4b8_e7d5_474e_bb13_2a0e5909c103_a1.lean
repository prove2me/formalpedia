-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:21:37.855418+00:00
-- url     : https://prove2.me/submissions/b049cfa4-5fe0-454c-b586-4a2b97b0b0dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     3 * Fintype.card V - 6 <= K.edgeFinset.card) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨L, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_lower_bound__p2m_0c026a9e_319c_4e6b_bdab_a1e6ad38d237_a1
      K hV hK
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  subst L
  simpa using hbound