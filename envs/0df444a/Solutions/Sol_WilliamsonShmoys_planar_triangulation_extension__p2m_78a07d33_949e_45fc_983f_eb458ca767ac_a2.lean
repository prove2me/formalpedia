-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:25.183282+00:00
-- url     : https://prove2.me/submissions/8022e1ef-19d4-4128-b01f-bbe3cd9092ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K /\ J <= K /\
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨K, hK, hJK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1 J hJ
  exact ⟨K, hK, hJK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
      K hK hmax hcard⟩
