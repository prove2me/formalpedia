-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:58:37.215924+00:00
-- url     : https://prove2.me/submissions/eb3f06b6-f093-471a-9ddf-362da09d242a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  have hExt :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1
      M hM hcard
  let N := Classical.choose hExt
  have hParts := Classical.choose_spec hExt
  have hMN : M <= N := hParts.1
  have hN : WilliamsonShmoys.HasPlanarDrawingOn N := hParts.2.1
  have hTri := hParts.2.2
  have hNM : N <= M := hMax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  let edgeCard : SimpleGraph V -> Nat := fun G => G.edgeFinset.card
  have hEqCard : M.edgeFinset.card = N.edgeFinset.card := by
    exact congrArg edgeCard hEq
  rw [hEqCard]
  exact hTri