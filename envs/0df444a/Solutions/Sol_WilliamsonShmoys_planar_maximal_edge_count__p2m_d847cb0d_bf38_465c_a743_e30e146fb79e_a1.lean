-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count__p2m_d847cb0d_bf38_465c_a743_e30e146fb79e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:22:02.911423+00:00
-- url     : https://prove2.me/submissions/cfc97d79-514b-49a0-937c-8c41c6bcf509
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L ->
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       L.edgeFinset.card <= K.edgeFinset.card)) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hup : K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
    simpa using
      WilliamsonShmoys.planar_edge_count_upper_bound__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
        K hK hcard
  have hext :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
      K hK hcard
  let L := Classical.choose hext
  have hproperty : K <= L /\ HasPlanarDrawingOn L /\
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       L.edgeFinset.card = 3 * Fintype.card V - 6) := Classical.choose_spec hext
  have hKL : K <= L := hproperty.1
  have hL : HasPlanarDrawingOn L := hproperty.2.1
  have htri : (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card = 3 * Fintype.card V - 6) := hproperty.2.2
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hmaxL : L.edgeFinset.card <= K.edgeFinset.card := by
    simpa using hmax L hKL hL
  have hlow : 3 * Fintype.card V - 6 <= K.edgeFinset.card := by
    calc
      3 * Fintype.card V - 6 = L.edgeFinset.card := by simpa using htri.symm
      _ <= K.edgeFinset.card := hmaxL
  change K.edgeFinset.card = 3 * Fintype.card V - 6
  omega