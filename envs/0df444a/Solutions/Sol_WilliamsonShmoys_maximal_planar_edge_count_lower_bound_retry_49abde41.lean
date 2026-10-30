-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_49abde41
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:54:09.853375+00:00
-- url     : https://prove2.me/submissions/dbf77b1b-2ea4-4922-a522-24d000a3988a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    (H.edgeSet.ncard : Int) >= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition H hH hmax hCard
  have hNat : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by
    omega
  have hInt : (3 * Fintype.card V : Int) = (H.edgeSet.ncard : Int) + 6 := by
    exact_mod_cast hNat
  omega