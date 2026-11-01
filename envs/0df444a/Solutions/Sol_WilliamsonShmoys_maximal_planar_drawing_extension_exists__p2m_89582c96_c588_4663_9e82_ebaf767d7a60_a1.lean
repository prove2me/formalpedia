-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:58.520805+00:00
-- url     : https://prove2.me/submissions/59bc2c2e-183c-41fa-980e-7c04995c17de

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  exact finite_simpleGraph_supergraph_maximal__p2m_55be6006_4b21_4039_be32_5973123fa254_a1
    K HasPlanarDrawingOn hK