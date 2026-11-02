-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:32.098978+00:00
-- url     : https://prove2.me/submissions/01106764-2f10-41a9-9c75-e8893ff2ab56

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel K.Adj := dK
       HasPlanarDrawingOn K ∧
       (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
         HasPlanarDrawingOn L →
         K.edgeFinset ⊆ L.edgeFinset →
         K.edgeFinset = L.edgeFinset) ∧
       H.edgeFinset ⊆ K.edgeFinset) := by
  classical
  obtain ⟨K, dK, h⟩ :=
    WilliamsonShmoys.finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
      (P := HasPlanarDrawingOn) H hH
  exact ⟨K, dK, h⟩