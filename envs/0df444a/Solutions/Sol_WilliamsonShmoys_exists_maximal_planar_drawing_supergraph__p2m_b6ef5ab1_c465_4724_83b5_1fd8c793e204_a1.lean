-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:53:13.100677+00:00
-- url     : https://prove2.me/submissions/dfe725dd-54c4-4838-8d74-4c234e41db36

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> Eq L K)) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
    H HasPlanarDrawingOn hH
