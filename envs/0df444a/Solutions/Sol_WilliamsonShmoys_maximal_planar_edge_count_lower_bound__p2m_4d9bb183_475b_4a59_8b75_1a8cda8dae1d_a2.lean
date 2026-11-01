-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:52:29.195513+00:00
-- url     : https://prove2.me/submissions/e55f51ff-d80b-4d83-9344-efef43f7bec8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_augmentation__p2m_064c0857_cede_4cc8_908c_7ab641b39ae5_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      L <= K -> HasPlanarDrawingOn K -> K = L) :
    letI : DecidableRel L.Adj := dL
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  obtain ⟨K, dK, hLK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_maximal_augmentation__p2m_064c0857_cede_4cc8_908c_7ab641b39ae5_a1
      L dL hL hcard
  have hEq : K = L := hmax K dK (show L <= K from hLK) hK
  subst K
  have hd : dK = dL := Subsingleton.elim _ _
  subst dK
  have hcount : L.edgeFinset.card = (3 * Fintype.card V - 6 : Nat) := by
    simpa only using hKcard
  exact Nat.le_of_eq hcount.symm