-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:04:34.725203+00:00
-- url     : https://prove2.me/submissions/2ac76393-3266-417c-aa62-892e29ff0d84

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K)
    (hV : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    letI : Fintype (↑K.edgeSet) := Fintype.ofFinite _
    3 * Fintype.card V <= K.edgeFinset.card + 6 := by
  classical
  obtain ⟨L, hKL, hL, htri⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
      K hK hV
  have hLK : L <= K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  have hbound := le_of_eq htri
  cases hEq
  exact hbound