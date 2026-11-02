-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:25.627886+00:00
-- url     : https://prove2.me/submissions/ae1fe446-8d9a-4b61-83de-7513bb78baf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> J <= K -> K <= J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    3 * Fintype.card V - 6 <= J.edgeFinset.card := by
  classical
  cases WilliamsonShmoys.planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
      J hJ hcard with
  | intro K hrest =>
      have hK := hrest.1
      have hJK := hrest.2.1
      have hKcard := hrest.2.2
      have hKJ : K <= J := hmax K hK hJK
      have hEq : J = K := le_antisymm hJK hKJ
      subst J
      omega
