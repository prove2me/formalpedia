-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:17.000631+00:00
-- url     : https://prove2.me/submissions/a743838f-53fd-4d15-a9be-256c5ba2f6a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel N.Adj := dN;
      N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hNK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1 N hN hcard
  have hKN : K = N := hmax K hNK hK
  subst K
  have hd : dN = Classical.decRel N.Adj := Subsingleton.elim _ _
  cases hd
  simpa using hCount