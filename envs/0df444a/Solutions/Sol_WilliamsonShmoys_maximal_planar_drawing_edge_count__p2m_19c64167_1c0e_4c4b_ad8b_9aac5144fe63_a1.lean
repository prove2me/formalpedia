-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:42.450345+00:00
-- url     : https://prove2.me/submissions/bebb2fc5-11e5-4739-87b8-2d110295c6e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) →
      T = U)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := dT
    T.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel T.Adj := dT
  obtain ⟨U, dU, hU, hTU, hUcard⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
      T dT hT hcard
  have hEq : T = U := hmax U dU hU hTU
  letI : DecidableRel U.Adj := dU
  have hFin : T.edgeFinset = U.edgeFinset := by
    cases hEq
    have hd : dT = dU := Subsingleton.elim _ _
    cases hd
    rfl
  rw [hFin]
  exact hUcard